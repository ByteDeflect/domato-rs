use std::{
    env,
    fs::{self, metadata},
    path::{Path, PathBuf},
    rc::Rc,
    str::FromStr,
};

use clap::Parser;
use domato::grammar::{Grammar, Variable};
use element::{Element, HtmlElement};
use rand::{seq::SliceRandom, thread_rng};
use regex::Captures;
use strum::VariantNames;

mod element;

macro_rules! regex {
    ($re:literal $(,)?) => {{
        static RE: once_cell::sync::OnceCell<regex::Regex> = once_cell::sync::OnceCell::new();
        RE.get_or_init(|| regex::Regex::new($re).unwrap())
    }};
}

#[derive(Clone)]
struct HtmlVariable {
    name: String,
    kind: Element,
}

impl Variable for HtmlVariable {
    fn get_name(&self) -> String {
        self.name.clone()
    }

    fn get_type(&self) -> String {
        self.kind.to_string()
    }
}

#[derive(Default)]
struct HtmlContext {
    htmlvars: Vec<HtmlVariable>,
    htmlvarctr: u32,
    svgvarctr: u32,
    mathmavarctr: u32,
    htmlvargen: String,
}

/// DOMATO (A DOM FUZZER)
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// File name which is to be generated in the same directory
    #[arg(long, short)]
    file: Option<String>,
    /// The output directory to put the generated files in
    #[arg(long, short)]
    output_dir: Option<String>,
    /// Number of files to be generated
    #[arg(long, short, default_value_t = 1)]
    no_of_files: usize,
    /// Template file you want to use
    #[arg(long, short, default_value=env::current_dir().unwrap().join("template.html").into_os_string())]
    template: PathBuf,
}
fn main() {
    let args = Args::parse();
    let template = fs::read_to_string(args.template).unwrap();
    if let Some(file) = args.file {
        generate_samples(&template, vec![file]);
    } else if let Some(output_dir) = args.output_dir {
        let nsamples = args.no_of_files;
        println!("Output directory: {}", output_dir);
        println!("Number of samples: {}", nsamples);
        match metadata(output_dir.clone()) {
            Err(_) => {
                fs::create_dir(output_dir.clone()).unwrap();
            }
            Ok(md) => {
                if !md.is_dir() {
                    panic!("{} is not the directory", output_dir);
                }
            }
        }
        let mut outfiles = Vec::new();
        for i in 0..nsamples {
            let path = Path::new(&output_dir);
            outfiles.push(
                path.join(format!("fuzz-{:05}.html", i))
                    .to_string_lossy()
                    .to_string(),
            );
        }
        generate_samples(&template, outfiles);
    }
}

fn generate_html_elements(ctx: &mut HtmlContext, n: i32) {
    for _ in 0..n {
        let tag = HtmlElement::VARIANTS.choose(&mut thread_rng()).unwrap();
        let tagtype = HtmlElement::from_str(tag).unwrap();
        ctx.htmlvarctr += 1;
        let varname = format!("htmlvar{}", ctx.htmlvarctr);
        ctx.htmlvars.push(HtmlVariable {
            name: varname.clone(),
            kind: Element::Html(tagtype),
        });
        ctx.htmlvargen = format!(
            "{} /* newvar{{{}:{}}} */ var{} = document.createElement(\"{}\"); // {}\n",
            ctx.htmlvargen, varname, tagtype, varname, tag, tagtype
        );
    }
}

fn generate_function_body(jsgrammar: &Grammar, htmlctx: &HtmlContext, num_lines: u32) -> String {
    let mut js = String::new();
    js += "var fuzzervars = {};\n\n";
    js += "SetVariable(fuzzervars, window, 'Window');\nSetVariable(fuzzervars, document, 'Document');\nSetVariable(fuzzervars, document.body.firstChild, 'Element');\n\n";
    js += "//beginjs\n";
    js += &htmlctx.htmlvargen;
    js += &jsgrammar
        .generate_code(num_lines, htmlctx.htmlvars.clone(), None)
        .unwrap();
    js += "\n//endjs\n";
    js += "var fuzzervars = {};\nfreememory()\n";

    js
}

/// Checks if grammar has errors and if so output them
#[allow(dead_code)]
fn check_grammar(grammar: Grammar) {
    for rule in grammar.all_rules {
        for part in &rule.parts {
            if part.kind == "text" {
                continue;
            }
            let tagname = &part.name;
            if grammar.creators.contains_key(tagname) {
                println!("No creators for type {}", tagname);
            }
        }
    }
}

fn generate_new_sample(
    template: &str,
    htmlgrammar: &Grammar,
    cssgrammar: &Grammar,
    jsgrammar: &Grammar,
) -> String {
    let mut result = template.to_string();
    let css = cssgrammar.generate_symbol("rules").unwrap();
    let html = htmlgrammar
        .generate_symbol("svgattr_marker-end_value")
        .unwrap();

    let mut htmlctx = HtmlContext::default();
    let re = regex!(r#"<[a-zA-Z0-9_-]+ "#);
    re.replace(&html, |m: &Captures| {
        let binding = m.get(0).unwrap().as_str();
        let tagname = &binding[1..binding.len() - 1];
        if let Ok(element) = Element::from_str(tagname) {
            let varname = match element {
                Element::Html(_) => {
                    htmlctx.htmlvarctr += 1;
                    format!("htmlvar{:05}", htmlctx.htmlvarctr)
                }
                Element::Svg(_) => {
                    htmlctx.svgvarctr += 1;
                    format!("svgvar{:05}", htmlctx.svgvarctr)
                }
                Element::MathMl(_) => {
                    htmlctx.mathmavarctr += 1;
                    format!("mathmlvar{:05}", htmlctx.mathmavarctr)
                }
            };
            htmlctx.htmlvars.push(HtmlVariable {
                name: varname.clone(),
                kind: element,
            });
            htmlctx.htmlvargen = format!(
                "{} /* newvar{{{}:{}}} */ var{} = document.getElementById(\"{}\");//{}\n",
                htmlctx.htmlvargen, varname, element, varname, varname, element
            );
            format!("{} id=\"{}\"", m.get(0).unwrap().as_str(), varname)
        } else {
            m.get(0).unwrap().as_str().to_string()
        }
    });

    generate_html_elements(&mut htmlctx, 5);

    result = result.replace("<cssfuzzer>", &css);
    result = result.replace("<htmlfuzzer>", &html);

    let mut handlers = false;
    while result.contains("<jsfuzzer>") {
        let mut numlines = 1000;
        if handlers {
            numlines = 500;
        } else {
            handlers = true;
        }
        result = result.replacen(
            "<jsfuzzer>",
            &generate_function_body(jsgrammar, &htmlctx, numlines),
            1,
        );
    }

    result
}

fn generate_samples(template: &str, outfiles: Vec<String>) {
    let grammar_dir = env::current_dir().unwrap().join("rules");

    let mut htmlgrammar = Grammar::new();
    htmlgrammar
        .parse_from_file(grammar_dir.join("html.txt").to_str().unwrap())
        .unwrap();

    let mut cssgrammar = Grammar::new();
    cssgrammar
        .parse_from_file(grammar_dir.join("css.txt").to_str().unwrap())
        .unwrap();

    let mut jsgrammar = Grammar::new();
    jsgrammar
        .parse_from_file(grammar_dir.join("js.txt").to_str().unwrap())
        .unwrap();

    let rccss = Rc::new(cssgrammar.clone());
    htmlgrammar.add_import("cssgrammar", rccss.clone());
    jsgrammar.add_import("cssgrammar", rccss);

    for outfile in outfiles {
        let result = generate_new_sample(template, &htmlgrammar, &cssgrammar, &jsgrammar);
        if !result.is_empty() {
            fs::write(outfile, result).unwrap();
        }
    }
}
