use std::{fmt::Display, str::FromStr};

use strum::EnumString;

#[derive(Clone, Debug)]
pub enum Kind {
    Builtin(BuiltinKind),
    Custom(String),
}

impl PartialEq<&str> for Kind {
    fn eq(&self, other: &&str) -> bool {
        let val = match self {
            Kind::Builtin(t) => t.to_string(),
            Kind::Custom(name) => name.to_string(),
        };
        val == **other
    }
}

impl From<String> for Kind {
    fn from(value: String) -> Self {
        Kind::from(value.as_str())
    }
}

impl From<&str> for Kind {
    fn from(value: &str) -> Self {
        match BuiltinKind::from_str(value) {
            Ok(t) => Kind::Builtin(t),
            Err(_) => Kind::Custom(value.to_string()),
        }
    }
}

impl Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Kind::Builtin(t) => write!(f, "{}", t),
            Kind::Custom(name) => write!(f, "{}", name),
        }
    }
}

impl Default for Kind {
    fn default() -> Self {
        Self::Custom(String::new())
    }
}

#[derive(Clone, Copy, EnumString, Debug)]
#[strum(serialize_all = "lowercase")]
pub enum BuiltinKind {
    Int,
    Int32,
    UInt32,
    Int8,
    UInt8,
    Int16,
    UInt16,
    Int64,
    UInt64,
    Float,
    Double,
    Char,
    String,
    HtmlSafeString,
    Hex,
    Import,
    Lines,
}

impl Display for BuiltinKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let r = match self {
            BuiltinKind::Int => "int",
            BuiltinKind::Int32 => "int32",
            BuiltinKind::UInt32 => "uint32",
            BuiltinKind::Int8 => "int8",
            BuiltinKind::UInt8 => "uint8",
            BuiltinKind::Int16 => "int16",
            BuiltinKind::UInt16 => "uint16",
            BuiltinKind::Int64 => "int64",
            BuiltinKind::UInt64 => "uint64",
            BuiltinKind::Float => "float",
            BuiltinKind::Double => "double",
            BuiltinKind::Char => "char",
            BuiltinKind::String => "string",
            BuiltinKind::HtmlSafeString => "htmlsafestring",
            BuiltinKind::Hex => "hex",
            BuiltinKind::Import => "import",
            BuiltinKind::Lines => "lines",
        };
        write!(f, "{}", r)
    }
}
