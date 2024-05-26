use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    fs, io,
    path::Path,
    rc::Rc,
    str::FromStr,
};

use bisection::bisect_left_by;
use rand::{
    seq::{IteratorRandom, SliceRandom},
    thread_rng, Rng,
};
use strum::EnumString;
use thiserror::Error;

use crate::{
    kind::{BuiltinKind, Kind},
    regex_utils::RegexSpit,
};

macro_rules! regex {
    ($re:literal $(,)?) => {{
        static RE: once_cell::sync::OnceCell<regex::Regex> = once_cell::sync::OnceCell::new();
        RE.get_or_init(|| regex::Regex::new($re).unwrap())
    }};
}

lazy_static! {
    static ref INT_RANGES: HashMap<&'static str, [i128; 2]> = HashMap::from([
        ("int", [-2147483648, 2147483647]),
        ("int32", [-2147483648, 2147483647]),
        ("uint32", [0, 4294967295]),
        ("int8", [-128, 127]),
        ("uint8", [0, 255]),
        ("int16", [-32768, 32767]),
        ("uint16", [0, 65536]),
        ("int64", [-9223372036854775808, 9223372036854775807]),
        ("uint64", [0, 18446744073709551615])
    ]);
}

const NONINTERESTING_TYPES: [&str; 6] =
    ["short", "long", "DOMString", "boolean", "float", "double"];

#[derive(Clone, Copy, EnumString, Debug)]
#[strum(serialize_all = "lowercase")]
enum Command {
    VarFormat,
    Include,
    Import,
    LineGuard,
    MaxRecursion,
    VarReuseProb,
    Extends,
}

impl Display for Command {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let r = match self {
            Command::VarFormat => "varformat",
            Command::Include => "include",
            Command::Import => "import",
            Command::LineGuard => "lineguard",
            Command::MaxRecursion => "max_recursion",
            Command::VarReuseProb => "var_reuse_prob",
            Command::Extends => "extends",
        };
        write!(f, "{}", r)
    }
}

#[derive(Error, Debug)]
pub enum GrammarError {
    #[error("Failed to parse '{}'", .0)]
    Parsing(String),
    #[error("Not builtin type: {}", .0)]
    Type(#[from] strum::ParseError),
    #[error("No type {} in creators", .0)]
    NoCreators(String),
    #[error("Maximum recursion level reached while creating object of  type {}", .0)]
    Recursion(String),
    #[error("Cannot find attribute '{}' in {} tag", .0, .1)]
    MissAttribute(String, String),
    #[error("Can read file: {}", .0)]
    Io(#[from] io::Error),
    #[error("Not root element is defined")]
    NoRoot,
}

#[derive(Clone, Debug, Default)]
pub struct Tag {
    pub name: String,
    pub kind: Kind,
    attributes: HashMap<String, String>,
}

impl Tag {
    fn get(&self, key: impl ToString) -> Option<&String> {
        self.attributes.get(&key.to_string())
    }

    fn get_default<T: FromStr>(&self, key: impl ToString, default_val: T) -> T {
        if let Some(value) = self.get(key) {
            value.parse::<T>().unwrap_or(default_val)
        } else {
            default_val
        }
    }

    fn insert(&mut self, key: impl ToString, value: impl ToString) -> Option<String> {
        self.attributes.insert(key.to_string(), value.to_string())
    }

    fn contains_key(&self, key: impl ToString) -> bool {
        self.attributes.contains_key(&key.to_string())
    }
}

pub trait Variable {
    fn get_name(&self) -> String;
    fn get_type(&self) -> String;
}

struct BuiltinVariable {
    name: String,
    kind: Kind,
}

impl Variable for BuiltinVariable {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn get_type(&self) -> String {
        self.kind.to_string()
    }
}

#[derive(Clone, Default)]
pub struct Rule {
    /// It should be named to `type` but `type` is conflicted with default rust's keyword
    kind: Kind,
    pub parts: Vec<Rc<Tag>>,
    pub creates: Vec<Rc<Tag>>,
    recursive: bool,
}

#[derive(Clone, Default)]
struct Context {
    lastvar: u32,
    lines: Vec<Rc<String>>,
    variables: HashMap<String, Vec<Rc<String>>>,
    interesting_lines: Vec<u32>,
    force_var_reuse: bool,
}

#[derive(Clone)]
pub struct Grammar {
    root: String,
    pub creators: HashMap<String, Vec<Rc<Rule>>>,
    pub nonrecursive_creators: HashMap<String, Vec<Rc<Rule>>>,
    pub all_rules: Vec<Rc<Rule>>,
    interesting_lines: HashMap<String, Vec<u32>>,
    all_nonhelper_lines: Vec<u32>,
    creator_cdfs: HashMap<String, Vec<f32>>,
    nonrecursivecreator_cdfs: HashMap<String, Vec<f32>>,
    // var_format: &'static str,
    definitions_dir: String,
    imports: HashMap<String, Rc<Grammar>>,
    line_guard: String,
    recursion_max: u32,
    var_reuse_prob: f32,
    interesting_line_prob: f32,
    max_vars_of_same_type: u32,
    inheritance: HashMap<String, Vec<Rc<String>>>,
    constant_types: HashMap<&'static str, char>,
}

impl Grammar {
    pub fn new() -> Self {
        Self {
            root: "".to_string(),
            creators: HashMap::new(),
            nonrecursive_creators: HashMap::new(),
            all_rules: Vec::new(),
            interesting_lines: HashMap::new(),
            all_nonhelper_lines: Vec::new(),
            creator_cdfs: HashMap::new(),
            nonrecursivecreator_cdfs: HashMap::new(),
            // var_format: "var{:#5d}",
            definitions_dir: String::from("."),
            imports: HashMap::new(),
            line_guard: String::new(),
            recursion_max: 50,
            var_reuse_prob: 0.75,
            interesting_line_prob: 0.9,
            max_vars_of_same_type: 5,
            inheritance: HashMap::new(),
            constant_types: HashMap::from([
                ("lt", '<'),
                ("gt", '>'),
                ("hash", '#'),
                ("cr", 13 as char),
                ("lf", 10 as char),
                ("space", ' '),
                ("tab", 9 as char),
                ("ex", '!'),
            ]),
        }
    }

    /// Generates integer types
    fn generate_int(&self, tag: &Tag) -> Result<String, GrammarError> {
        let tag_name = tag.name.clone();
        let default_range = INT_RANGES
            .get(tag_name.as_str())
            .unwrap_or_else(|| panic!("Cannot generate {} for integer type", tag_name));

        let min_value = tag.get_default("min", default_range[0]);
        let max_value = tag.get_default("max", default_range[1]);
        if min_value > max_value {
            panic!(
                "Cannot generate an integer in range ({},{})",
                min_value, max_value
            );
        }

        let i = thread_rng().gen_range(min_value..=max_value);
        // TODO: missing packing int here
        Ok(i.to_string())
    }

    /// Generates floating point types
    fn generate_float(&self, tag: &Tag) -> Result<String, GrammarError> {
        let min_value = tag.get_default("min", 0.0);
        let max_value = tag.get_default("max", 1.0);
        if min_value > max_value {
            panic!(
                "Cannot generate a float in range ({}, {})",
                min_value, max_value
            );
        }

        let f = min_value + rand::random::<f64>() * (max_value - min_value);
        // TODO: missing packing float here
        Ok(f.to_string())
    }

    /// Generates a single character
    fn generate_char(&self, tag: &Tag) -> Result<String, GrammarError> {
        if let Some(code) = tag.get("code") {
            return Ok(String::from(
                code.parse::<u8>()
                    .unwrap_or_else(|_| panic!("Cannot convert {} to ascii a character", code))
                    as char,
            ));
        }

        let min_value: u8 = tag.get_default("min", 0);
        let max_value = tag.get_default("max", 255);
        if min_value > max_value {
            panic!(
                "Cannot generate a ascii character in range ({}, {})",
                min_value, max_value
            );
        }

        Ok(String::from(
            thread_rng().gen_range(min_value..=max_value) as char
        ))
    }

    /// Generates a random string
    fn generate_string(&self, tag: &Tag) -> Result<String, GrammarError> {
        let min_value: u8 = tag.get_default("min", 0);
        let max_value = tag.get_default("max", 255);
        if min_value > max_value {
            panic!(
                "Cannot generate a string with ascii characters in range ({}, {})",
                min_value, max_value
            );
        }

        let minlen = tag.get_default("minlength", 0);
        let maxlen = tag.get_default("maxlength", 20);
        if minlen > maxlen {
            panic!(
                "Cannot generate a random string in length range ({}, {})",
                minlen, maxlen
            );
        }

        let mut rng = thread_rng();
        let lenth = rng.gen_range(minlen..=maxlen);

        let mut result = String::new();
        for _ in 0..lenth {
            result += &String::from(rng.gen_range(min_value..=max_value) as char);
        }
        Ok(result)
    }

    /// Generates a random html string
    fn generate_html_string(&self, tag: &Tag) -> Result<String, GrammarError> {
        Ok(html_escape::encode_safe(&self.generate_string(tag)?).to_string())
    }

    /// Generates a random hex string
    fn generate_hex(&self, tag: &Tag) -> Result<String, GrammarError> {
        let digit = thread_rng().gen_range(0..16);
        if tag.contains_key("up") {
            Ok(format!("{:#X}", digit))
        } else {
            Ok(format!("{:#x}", digit))
        }
    }

    /// Expands a symbol from another (imported) grammar
    fn generate_import(&self, tag: &Tag) -> Result<String, GrammarError> {
        if let Some(grammarname) = tag.get("from") {
            if let Some(grammar) = self.imports.get(grammarname) {
                if let Some(symbol) = tag.get("symbol") {
                    grammar.generate_symbol(symbol)
                } else {
                    grammar.generate_root()
                }
            } else {
                panic!("Cannot get {} from imported grammars", grammarname);
            }
        } else {
            Err(GrammarError::MissAttribute(
                "from".to_string(),
                tag.kind.to_string(),
            ))
        }
    }

    /// Generates a give number of lines of code
    fn generate_lines(&self, tag: &Tag) -> Result<String, GrammarError> {
        if tag.contains_key("count") {
            let num_lines = tag.get_default("count", 1);
            self.generate_code(num_lines, Vec::<BuiltinVariable>::new(), None)
        } else {
            Err(GrammarError::MissAttribute(
                "count".to_string(),
                tag.kind.to_string(),
            ))
        }
    }

    /// Generates a given number of lines of code
    pub fn generate_code(
        &self,
        num_lines: u32,
        initial_variable: Vec<impl Variable>,
        last_var: Option<u32>,
    ) -> Result<String, GrammarError> {
        let mut context = Context {
            lastvar: last_var.unwrap_or(0),
            ..Default::default()
        };

        for v in initial_variable {
            self.add_variable(&v.get_name(), &v.get_type().to_string(), &mut context);
        }
        self.add_variable("document", "Document", &mut context);
        self.add_variable("window", "Window", &mut context);

        while (context.lines.len() as u32) < num_lines {
            let mut tmp_context = context.clone();
            let mut rng = thread_rng();
            let lineno: &u32;
            if rand::random::<f32>() < self.interesting_line_prob
                && !tmp_context.interesting_lines.is_empty()
            {
                tmp_context.force_var_reuse = true;
                lineno = tmp_context.interesting_lines.choose(&mut rng).unwrap();
            } else {
                lineno = self.all_nonhelper_lines.choose(&mut rng).unwrap();
            }
            let creators = self
                .creators
                .get("line")
                .unwrap()
                .get(*lineno as usize)
                .unwrap();
            match self.expand_rule("line", creators, &mut tmp_context, 0, false) {
                Ok(_) => context = tmp_context,
                Err(e) => println!("Error: {}", e),
            }
        }
        let mut guarded_lines = Vec::new();
        if self.line_guard.is_empty() {
            guarded_lines = context.lines;
        } else {
            for line in context.lines {
                guarded_lines.push(self.line_guard.replace("<line>", &line).into());
            }
        }
        let r: Vec<&str> = guarded_lines.iter().map(|line| line.as_str()).collect();
        Ok(r.join("\n"))
    }

    /// Executes user-defined python code
    fn exec_function(
        &self,
        _function_name: String,
        _attributes: &Tag,
        _context: &mut Context,
        _ret_val: String,
    ) -> String {
        // TODO
        todo!("We cannot run Python code in Rust");
    }

    fn select_creator(
        &self,
        symbol: &str,
        recursion_depth: u32,
        force_nonrecursive: bool,
    ) -> Result<Rc<Rule>, GrammarError> {
        let creators: &Vec<Rc<Rule>>;
        if !self.creators.contains_key(symbol) {
            return Err(GrammarError::NoCreators(symbol.to_string()));
        }

        if recursion_depth >= self.recursion_max {
            return Err(GrammarError::Recursion(symbol.to_string()));
        }

        let cdf = if force_nonrecursive && self.nonrecursive_creators.contains_key(symbol) {
            creators = self.nonrecursive_creators.get(symbol).unwrap();
            self.nonrecursivecreator_cdfs
                .get(symbol)
                .unwrap_or_else(|| panic!("Cannot get '{symbol}' from nonrecursivecreator_cdfs"))
        } else {
            creators = self.creators.get(symbol).unwrap();
            self.creator_cdfs
                .get(symbol)
                .unwrap_or_else(|| panic!("Cannot get '{symbol}' from creator_cdfs"))
        };

        let mut rng = thread_rng();
        if cdf.is_empty() {
            return Ok(creators.choose(&mut rng).unwrap().clone());
        }

        let f = |a: &f32, b: &f32| a.partial_cmp(b).unwrap();
        let idx = bisect_left_by(cdf, |a| f(a, &rand::random::<f32>()));
        Ok(creators[idx].clone())
    }

    fn generate(
        &self,
        symbol: &str,
        context: &mut Context,
        recursion_depth: Option<u32>,
        force_nonrecursive: Option<bool>,
    ) -> Result<String, GrammarError> {
        let recursion_depth = recursion_depth.unwrap_or(0);
        let force_nonrecursive = force_nonrecursive.unwrap_or(false);
        let force_var_reuse = context.force_var_reuse;

        if context.variables.contains_key(symbol)
            && !NONINTERESTING_TYPES.contains(&symbol)
            && (force_var_reuse
                || rand::random::<f32>() < self.var_reuse_prob
                || context.variables.get(symbol).unwrap().len()
                    > self.max_vars_of_same_type.try_into().unwrap())
        {
            context.force_var_reuse = false;
            let variables = context.variables.get(symbol).unwrap();
            return Ok(variables.choose(&mut thread_rng()).unwrap().to_string());
        }
        match self.select_creator(symbol, recursion_depth, force_nonrecursive) {
            Ok(creators) => self.expand_rule(
                symbol,
                &creators,
                context,
                recursion_depth,
                force_nonrecursive,
            ),
            Err(err) => Err(err),
        }
    }

    fn expand_rule(
        &self,
        symbol: &str,
        rule: &Rule,
        context: &mut Context,
        recursion_depth: u32,
        force_nonrecursive: bool,
    ) -> Result<String, GrammarError> {
        let mut variable_ids: HashMap<String, String> = HashMap::new();
        let mut new_vars: Vec<BuiltinVariable> = Vec::new();
        let mut ret_vars: Vec<String> = Vec::new();
        let mut ret_parts: Vec<String> = Vec::new();
        let mut expanded = String::new();

        for part in &rule.parts {
            if let Some(id) = part.get("id") {
                if let Some(var_id) = variable_ids.get(id) {
                    ret_parts.push(var_id.to_owned());
                    continue;
                }
            }

            if part.kind == "text" {
                expanded = part.get("text").unwrap().to_string();
            } else if rule.kind == "code" && part.contains_key("new") {
                let var_type = part.name.clone();
                context.lastvar += 1;
                // TODO: we need dymamic formatter here, replacing for `self.var_format`
                let var_name = format!("var{:05}", context.lastvar);
                new_vars.push(BuiltinVariable {
                    name: var_name.clone(),
                    kind: Kind::from(var_type.clone()),
                });
                if var_type.clone() == symbol {
                    ret_vars.push(var_name.clone());
                }
                expanded = "/* newvar{".to_owned()
                    + &var_name.clone()
                    + ":"
                    + &var_type
                    + "} */ var "
                    + &var_name;
            } else if let Some(ctype) = self.constant_types.get(part.name.as_str()) {
                expanded = ctype.to_string();
            } else if BuiltinKind::from_str(part.name.as_str()).is_ok() {
                expanded = match self.generate_builtin_type(part) {
                    Ok(o) => o,
                    Err(e) => return Err(e),
                };
            } else if part.name == "call" {
                if let Some(function) = part.get("function") {
                    expanded =
                        self.exec_function(function.to_string(), part, context, String::new())
                }
            } else if part.name == "any" && !context.variables.is_empty() {
                expanded = self.get_any_var(context);
            } else {
                expanded = match self.generate(
                    &part.name,
                    context,
                    Some(recursion_depth + 1),
                    Some(force_nonrecursive),
                ) {
                    Ok(ok) => ok,
                    Err(GrammarError::Recursion(e)) => {
                        if !force_nonrecursive {
                            match self.generate(
                                &part.name,
                                context,
                                Some(recursion_depth + 1),
                                Some(true),
                            ) {
                                Ok(r) => r,
                                Err(e) => return Err(e),
                            }
                        } else {
                            return Err(GrammarError::Recursion(e));
                        }
                    }
                    Err(e) => return Err(e),
                }
            }

            if let Some(id) = part.get("id") {
                variable_ids.insert(id.to_string(), expanded.clone());
            }

            if let Some(before) = part.get("beforeoutput") {
                expanded = self.exec_function(before.to_string(), part, context, expanded);
            }
            ret_parts.push(expanded.clone());
        }
        // Add all newly created variables to the context
        let mut additional_lines = Vec::new();
        for v in new_vars {
            if NONINTERESTING_TYPES.contains(&v.kind.to_string().as_str()) {
                self.add_variable(&v.name, &v.kind.to_string(), context);
                additional_lines.push(Rc::new(format!(
                    "if (!{}) {{{} = GetVariable(fuzzervars, {}); }} else {{ {} }}",
                    v.name,
                    v.name,
                    v.kind,
                    self.get_variable_setters(&v.name, &v.kind.to_string())
                )));
            }
        }

        // Return the result.
        // In case of 'ordinary' grammar rules, return the filled rule.
        // In case of code, return just the variable name
        // and update the context
        let filled_rule = ret_parts.join("");
        if rule.kind == "grammar" {
            Ok(filled_rule)
        } else {
            context.lines.push(Rc::new(filled_rule.clone()));
            context.lines.append(&mut additional_lines);
            if symbol == "line" {
                Ok(filled_rule)
            } else {
                let mut rng = thread_rng();
                Ok(ret_vars.choose(&mut rng).unwrap().to_string())
            }
        }
    }

    /// Expands root symbol
    pub fn generate_root(&self) -> Result<String, GrammarError> {
        if !self.root.is_empty() {
            let mut context = Context::default();
            self.generate(&self.root, &mut context, Some(0), None)
        } else {
            Err(GrammarError::NoRoot)
        }
    }

    /// Expands a symbol whose name is given as an argument
    pub fn generate_symbol(&self, name: &str) -> Result<String, GrammarError> {
        let mut context = Context::default();
        self.generate(name, &mut context, Some(0), None)
    }

    fn get_cdf(&self, symbol: String, creators: &Vec<Rc<Rule>>) -> Vec<f32> {
        let mut uniform = true;
        let mut probabilities = Vec::new();
        let mut defined = Vec::new();
        let mut cdf = Vec::new();
        let mut create_tag = &Tag::default();

        if symbol == "line" {
            // We can't currently set line probability
            return Vec::new();
        }

        // Get probabilities for individual rule
        for creator in creators {
            if creator.kind == "grammar" {
                create_tag = creator.creates.first().unwrap();
            } else {
                // For type=code multiple variables may be created
                for tag in &creator.creates {
                    if tag.name == symbol {
                        create_tag = tag;
                        break;
                    }
                }
            }

            if let Some(p) = create_tag.get("p") {
                probabilities.push(p.parse::<f32>().unwrap());
                defined.push(true);
                uniform = false;
            } else {
                probabilities.push(0.0);
                defined.push(false);
            }
        }

        if uniform {
            return Vec::new();
        }

        // Compute probabilities for rules in which they are not
        // explicitly defined
        // Also normalize probabilities in case where sum > 1
        let mut nondef_value = 0.0;
        let mut norm_factor = 1.0;
        let mut p_sum: f32 = probabilities.iter().sum();
        let nondef_count = defined.iter().filter(|x| !(**x)).count() as f32;
        if p_sum > 1.0 || nondef_count == 0.0 {
            norm_factor = 1.0 / p_sum;
        } else {
            nondef_value = (1.0 - p_sum) / nondef_count;
        }
        p_sum = 0.0;

        for i in 0..probabilities.len() {
            let mut p = probabilities[i];
            if !defined[i] {
                p = nondef_value;
            } else {
                p *= norm_factor;
            }
            p_sum += p;
            cdf.push(p_sum);
        }
        cdf
    }

    /// Preprocessess probabilities for production rules
    ///
    /// Creates CDFs (cumulative distribution functions) and normalizes
    /// probabilities in the [0,1] range for all creators. This is a
    /// preprocessing function that makes subsequent creator selection
    /// based on probability easier.
    fn normalize_probabilities(&mut self) {
        for (symbol, creators) in self.creators.iter() {
            let cdf = self.get_cdf(symbol.to_string(), creators);
            self.creator_cdfs.insert(symbol.to_string(), cdf);
        }

        for (symbol, creators) in self.nonrecursive_creators.iter() {
            let cdf = self.get_cdf(symbol.to_string(), creators);
            self.nonrecursivecreator_cdfs
                .insert(symbol.to_string(), cdf);
        }
    }

    /// Extracts tag name and attributes from a string
    fn parse_tag_and_attributes(&self, s: &str) -> Result<Tag, GrammarError> {
        let parts: Vec<&str> = s.split_whitespace().collect();
        if parts.is_empty() {
            return Err(GrammarError::Parsing(s.to_string()));
        }
        let mut ret = Tag {
            kind: Kind::from("tag"),
            ..Default::default()
        };
        let attrstart;
        if parts.len() > 1 && parts[0] == "new" {
            ret.name = parts[1].to_string();
            ret.insert("new", "true");
            attrstart = 2;
        } else {
            ret.name = parts[0].to_string();
            attrstart = 1;
        }
        let mut i = 0;
        while i < parts.len() {
            let attrparts: Vec<&str> = parts[i].split('=').collect();
            if attrparts.len() == 2 {
                ret.insert(attrparts[0], attrparts[1]);
            } else if attrparts.len() == 1 {
                ret.insert(attrparts[0], "true");
            } else {
                return Err(GrammarError::Parsing(parts[i].to_string()));
            }
            i += attrstart;
        }
        Ok(ret)
    }

    /// Parses a rule for generation code
    fn parse_code_line(
        &mut self,
        line: &str,
        helper_lines: Option<bool>,
    ) -> Result<(), GrammarError> {
        let helper_lines = helper_lines.unwrap_or(false);
        let mut rule = Rule {
            kind: Kind::from("code"),
            ..Default::default()
        };
        // Splits the line into constant parts and tags. For example
        // "foo<bar>baz" would be split into three parts, "foo", "bar" and "baz"
        // Every other part is going to be constant and every other part
        // is going to be a tag, always starting with a constant. Empty
        // spaces between tags/beginning/end are not a problem because
        // then empty strings will be returned in corresponding places,
        // for example "<foo><bar>" gets split into "", "foo", "", "bar"
        let re = regex!(r"<([^>)]*)>");
        let rule_parts: Vec<&str> = re.split_inclusive_iter(line).collect();
        for (i, part) in rule_parts.iter().enumerate() {
            if i % 2 == 0 {
                if !part.is_empty() {
                    let mut tag = Tag {
                        kind: Kind::from("text"),
                        ..Default::default()
                    };
                    tag.insert("text", part);
                    rule.parts.push(Rc::new(tag));
                }
            } else {
                let parsedtag = Rc::new(self.parse_tag_and_attributes(&part[1..part.len() - 1])?);
                rule.parts.push(parsedtag.clone());
                if parsedtag.contains_key("new") {
                    rule.creates.push(parsedtag);
                }
            }
        }

        let rule = Rc::new(rule);
        for tag in &rule.creates {
            if NONINTERESTING_TYPES.contains(&tag.name.as_str()) {
                continue;
            }
            if let Some(creator) = self.creators.get_mut(&tag.name) {
                creator.push(rule.clone());
            } else {
                self.creators.insert(tag.name.clone(), vec![rule.clone()]);
            }
            if tag.contains_key("nonrecursive") {
                if let Some(creator) = self.nonrecursive_creators.get_mut(&tag.name) {
                    creator.push(rule.clone());
                } else {
                    self.nonrecursive_creators
                        .insert(tag.name.clone(), vec![rule.clone()]);
                }
            }
        }

        if !helper_lines {
            if let Some(creator) = self.creators.get_mut("line") {
                creator.push(rule.clone());
            } else {
                self.creators.insert("line".to_string(), vec![rule.clone()]);
            }
        }

        self.all_rules.push(rule);
        Ok(())
    }

    /// Parses a grammar rule
    fn parse_grammar_line(&mut self, line: &str) -> Result<(), GrammarError> {
        let re = regex!(r"^<([^>]*)>\s*=\s*(.*)$");
        let captures = re.captures(line).unwrap();
        if captures.len() != 3 {
            return Err(GrammarError::Parsing(line.to_string()));
        }
        let mut rule = Rule {
            kind: Kind::from("grammar"),
            creates: vec![Rc::new(
                self.parse_tag_and_attributes(captures.get(1).unwrap().as_str())
                    .unwrap(),
            )],
            ..Default::default()
        };
        let re2 = regex!(r"<[^>)]*>");
        let rule_parts: Vec<&str> = re2
            .split_inclusive_iter(captures.get(2).unwrap().as_str())
            .collect();
        rule.recursive = false;

        // Splits the line into constant parts and tags. For example
        // "foo<bar>baz" would be split into three parts, "foo", "bar" and "baz"
        // Every other part is going to be constant and every other part
        // is going to be a tag, always starting with a constant. Empty
        // spaces between tags/beginning/end are not a problem because
        // then empty strings will be returned in corresponding places,
        // for example "<foo><bar>" gets split into "", "foo", "", "bar"
        for (i, part) in rule_parts.iter().enumerate() {
            if i % 2 == 0 {
                if !part.is_empty() {
                    let mut tag = Tag {
                        kind: Kind::from("text"),
                        ..Default::default()
                    };
                    tag.insert("text", part);
                    rule.parts.push(Rc::new(tag));
                }
            } else {
                let parsedtag = Rc::new(self.parse_tag_and_attributes(&part[1..part.len() - 1])?);
                rule.parts.push(parsedtag.clone());
                if let Some(first) = rule.creates.first() {
                    if parsedtag.name == first.name {
                        rule.recursive = true;
                    }
                }
            }
        }

        let rule = Rc::new(rule);
        // Store the rule in appropriate sets
        let tag = rule.creates.first().unwrap();
        if let Some(creator) = self.creators.get_mut(&tag.name) {
            creator.push(rule.clone());
        } else {
            self.creators.insert(tag.name.clone(), vec![rule.clone()]);
        }
        if tag.contains_key("nonrecursive") {
            if let Some(creator) = self.nonrecursive_creators.get_mut(&tag.name) {
                creator.push(rule.clone());
            } else {
                self.nonrecursive_creators
                    .insert(tag.name.clone(), vec![rule.clone()]);
            }
        }
        self.all_rules.push(rule.clone());
        if tag.contains_key("root") {
            self.root.clone_from(&tag.name);
        }
        Ok(())
    }

    /// Removes comments and trims the line
    fn remove_comments<'a>(&self, line: &'a str) -> &'a str {
        if line.starts_with('#') {
            ""
        } else {
            line.strip_suffix('#').unwrap_or(line).trim()
        }
    }
    /// Fixes indentation in user-defined functions.
    ///
    /// Exec requires zero first-level indentation. This function fixes
    /// it by finding a minimum indentation in code and removing it
    /// from all lines
    #[allow(dead_code)]
    fn fix_indents(self, source: String) -> String {
        // Tab is 8 spaces according to Python documentation.
        let binding = source.replace('\t', " ".repeat(8).as_str());
        let lines: Vec<&str> = binding.split('\n').collect();
        let lines_without_blanks: Vec<&str> = lines.iter().map(|line| line.trim()).collect();
        let indent_to_remove: usize = lines_without_blanks
            .iter()
            .map(|line| line.len() - line.trim().len())
            .min()
            .unwrap();

        if indent_to_remove == 0 {
            return source;
        }

        let mut output = Vec::new();
        for mut ln in lines {
            if !ln.trim().is_empty() {
                ln = ln.split_at(indent_to_remove).0;
            }
            output.push(ln);
        }
        output.join("\n")
    }

    fn save_function(&self, _name: &str, _source: &str) -> Result<(), GrammarError> {
        todo!()
    }

    fn set_variable_format(&self, _var_format: &str) -> Result<(), GrammarError> {
        todo!()
    }

    fn set_line_guard(&mut self, lineguard: &str) -> Result<(), GrammarError> {
        self.line_guard = lineguard.to_string();
        Ok(())
    }

    /// Sets maximum recursion depth
    fn set_recursion_depth(&mut self, depth_str: &str) -> Result<(), GrammarError> {
        self.recursion_max = depth_str
            .trim()
            .parse::<u32>()
            .unwrap_or(self.recursion_max);
        Ok(())
    }

    fn set_var_resue_probability(&mut self, p_str: &str) -> Result<(), GrammarError> {
        self.var_reuse_prob = p_str.trim().parse::<f32>().unwrap_or(self.var_reuse_prob);
        Ok(())
    }

    fn set_extends(&mut self, p_str: &str) -> Result<(), GrammarError> {
        let args: Vec<&str> = p_str.trim().split(' ').collect();
        let objectname = args[0];
        let parentname = args[1];
        if !self.inheritance.contains_key(objectname) {
            self.inheritance.insert(objectname.to_string(), Vec::new());
        }
        self.inheritance
            .get_mut(objectname)
            .unwrap()
            .push(Rc::new(parentname.to_string()));
        Ok(())
    }

    /// Imports a grammar from another file
    fn import_grammar(&mut self, filename: &str) -> Result<(), GrammarError> {
        let basename = Path::new(filename).file_name().unwrap();
        let binding = Path::new(&self.definitions_dir).join(filename);
        let path = binding.to_str().unwrap();
        let mut subgrammar = Grammar::new();
        subgrammar.parse_from_file(path)?;
        self.imports
            .insert(basename.to_str().unwrap().to_string(), Rc::new(subgrammar));
        Ok(())
    }

    /// Adds a grammar that can then be used from <import> tags.
    ///
    /// In case the grammar is already loaded this can be faster than
    /// using the !import directive which parses the file again.
    pub fn add_import(&mut self, name: &str, grammar: Rc<Grammar>) {
        self.imports.insert(name.to_string(), grammar);
    }

    fn include_from_string(&mut self, grammar_str: &str) -> Result<(), GrammarError> {
        let mut in_code = false;
        let mut helper_lines = false;
        let mut in_function = false;
        let lines = grammar_str.lines();
        let mut function_body = String::new();
        let mut function_name = "";
        let re1 = regex!(r"^!([a-z_]+)\s*(.*)$");
        let re2 = regex!(r"^function\s*([a-zA-Z._0-9]+)$");
        for line in lines {
            let mut cleanline = line;
            if !in_function {
                cleanline = self.remove_comments(cleanline);
                if cleanline.is_empty() {
                    continue;
                }
            }
            if let Some(m) = re1.captures(cleanline) {
                let command = m.get(1).unwrap().as_str();
                let params = m.get(2).unwrap().as_str();
                if let Ok(command) = Command::from_str(command) {
                    self.run_command(command, params)?;
                } else if command == "begin" && params == "lines" {
                    in_code = true;
                    helper_lines = false;
                } else if command == "begin" && params == "helperlines" {
                    in_code = true;
                    helper_lines = true;
                } else if command == "end" && ["lines", "helperlines"].contains(&params) {
                    if in_code {
                        in_code = false;
                    }
                } else if command == "begin" && params.starts_with("function") {
                    if let Some(m) = re2.captures(params) {
                        if !in_function {
                            function_name = m.get(1).unwrap().as_str();
                            function_body = String::new();
                            in_function = true;
                        } else {
                            return Err(GrammarError::Parsing(line.to_string()));
                        }
                    }
                } else if command == "end" && params == "function" {
                    if in_function {
                        in_function = false;
                        self.save_function(function_name, &function_body)?;
                    }
                } else {
                    return Err(GrammarError::Parsing(line.to_string()));
                }
                continue;
            }

            if in_function {
                function_body += cleanline;
                function_body += "\n";
            } else if in_code {
                self.parse_code_line(cleanline, Some(helper_lines))?;
            } else {
                self.parse_grammar_line(cleanline)?;
            }
        }
        Ok(())
    }

    fn include_from_file(&mut self, filename: &str) -> Result<(), GrammarError> {
        let path = Path::new(&self.definitions_dir).join(filename);
        match fs::read_to_string(path) {
            Ok(content) => self.parse_from_string(&content),
            Err(e) => Err(GrammarError::Io(e)),
        }
    }

    /// Parses grammar rules from string
    ///
    /// Splits the string into lines, parses the lines and loads grammar rules
    /// See readme for the rule syntax
    pub fn parse_from_string(&mut self, grammar_str: &str) -> Result<(), GrammarError> {
        self.include_from_string(grammar_str)?;
        self.normalize_probabilities();
        self.compute_interesting_indices();
        Ok(())
    }

    /// Parses grammar from file
    ///
    /// Opens a text file, parses it and loads the grammar rules within.
    /// See readme for the rule syntax. Note that grammar
    /// files can include other grammar files using !import command.
    pub fn parse_from_file(&mut self, filename: &str) -> Result<(), GrammarError> {
        match fs::read_to_string(filename) {
            Ok(content) => {
                let path = Path::new(filename);
                self.definitions_dir = path.parent().unwrap().to_str().unwrap().to_string();
                self.parse_from_string(&content)
            }
            Err(e) => Err(GrammarError::Io(e)),
        }
    }

    fn run_command(&mut self, command: Command, param: &str) -> Result<(), GrammarError> {
        match command {
            Command::VarFormat => self.set_variable_format(param),
            Command::Include => self.include_from_file(param),
            Command::Import => self.import_grammar(param),
            Command::LineGuard => self.set_line_guard(param),
            Command::MaxRecursion => self.set_recursion_depth(param),
            Command::VarReuseProb => self.set_var_resue_probability(param),
            Command::Extends => self.set_extends(param),
        }
    }

    fn compute_interesting_indices(&mut self) {
        if let Some(line) = self.creators.get("line") {
            for (i, rule) in line.iter().enumerate() {
                self.all_nonhelper_lines.push(i as u32);
                for part in &rule.parts {
                    if part.kind == "text" {
                        continue;
                    }
                    let tagname = part.name.to_owned();
                    if NONINTERESTING_TYPES.contains(&tagname.as_str()) {
                        continue;
                    }
                    if part.contains_key("new") {
                        continue;
                    }
                    if !self.interesting_lines.contains_key(&tagname) {
                        self.interesting_lines.insert(tagname.clone(), Vec::new());
                    }
                    if let Some(lines) = self.interesting_lines.get_mut(&tagname) {
                        lines.push(i as u32);
                    }
                }
            }
        }
    }

    fn add_variable(&self, var_name: &str, var_type: &str, context: &mut Context) {
        if !context.variables.contains_key(var_type) {
            context.variables.insert(String::from(var_type), Vec::new());
            if let Some(types) = self.interesting_lines.get(var_type) {
                let set1: HashSet<u32> =
                    HashSet::from_iter(context.interesting_lines.iter().cloned());
                let set2 = HashSet::from_iter(types.iter().cloned());
                let new_interesting = &set2 - &set1;
                context
                    .interesting_lines
                    .append(&mut new_interesting.into_iter().collect::<Vec<u32>>());
            }
        }
        if let Some(vars) = context.variables.get_mut(var_type) {
            vars.push(Rc::new(var_name.to_string()));
        }

        if let Some(types) = self.inheritance.get(var_type) {
            for parent_type in types {
                self.add_variable(var_name, parent_type, context);
            }
        }
    }

    fn get_variable_setters(&self, var_name: &str, var_type: &str) -> String {
        let mut ret = format!("SetVariable(fuzzervars, {}, {});", var_name, var_type);
        if let Some(vars) = self.inheritance.get(var_type) {
            for parent_type in vars {
                ret += &self.get_variable_setters(var_name, parent_type);
            }
        }
        ret
    }

    fn get_any_var(&self, context: &Context) -> String {
        let mut rng = thread_rng();
        let var_type = context
            .variables
            .keys()
            .choose(&mut rng)
            .unwrap_or_else(|| panic!("context.variables is empty"));
        context
            .variables
            .get(var_type)
            .unwrap()
            .choose(&mut rng)
            .unwrap()
            .to_string()
    }

    fn generate_builtin_type(&self, tag: &Tag) -> Result<String, GrammarError> {
        match BuiltinKind::from_str(&tag.name) {
            Ok(t) => match t {
                BuiltinKind::Int => self.generate_int(tag),
                BuiltinKind::Int32 => self.generate_int(tag),
                BuiltinKind::UInt32 => self.generate_int(tag),
                BuiltinKind::Int8 => self.generate_int(tag),
                BuiltinKind::UInt8 => self.generate_int(tag),
                BuiltinKind::Int16 => self.generate_int(tag),
                BuiltinKind::UInt16 => self.generate_int(tag),
                BuiltinKind::Int64 => self.generate_int(tag),
                BuiltinKind::UInt64 => self.generate_int(tag),
                BuiltinKind::Float => self.generate_float(tag),
                BuiltinKind::Double => self.generate_float(tag),
                BuiltinKind::Char => self.generate_char(tag),
                BuiltinKind::String => self.generate_string(tag),
                BuiltinKind::HtmlSafeString => self.generate_html_string(tag),
                BuiltinKind::Hex => self.generate_hex(tag),
                BuiltinKind::Import => self.generate_import(tag),
                BuiltinKind::Lines => self.generate_lines(tag),
            },
            Err(e) => Err(GrammarError::Type(e)),
        }
    }
}
