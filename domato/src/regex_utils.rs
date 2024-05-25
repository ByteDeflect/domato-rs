// References:
// 1. https://github.com/rust-lang/regex/issues/330#issuecomment-274058261
// 2. https://github.com/rust-lang/regex/pull/1096

use regex::{Match, Matches, Regex};

pub trait RegexSpit {
    fn split_inclusive_iter<'r, 't>(&'r self, text: &'t str) -> SplitInclusive<'r, 't>;
}

pub struct SplitInclusive<'r, 't> {
    finder: Matches<'r, 't>,
    prev: Option<Match<'t>>,
    last: usize,
    text: &'t str,
    idx: usize,
}

impl<'r, 't> Iterator for SplitInclusive<'r, 't> {
    type Item = &'t str;

    fn next(&mut self) -> Option<Self::Item> {
        if self.prev.is_none() {
            if let Some(m) = self.finder.next() {
                self.prev = Some(m);
            } else if self.last == self.text.len() {
                return None;
            } else {
                let s = &self.text[self.last..];
                self.last = self.text.len();
                return Some(s);
            }
        };
        let prev = self.prev.unwrap();
        let r = if self.idx % 2 == 0 {
            if self.last == prev.start() {
                Some("")
            } else {
                Some(&self.text[self.last..prev.start()])
            }
        } else {
            self.last = prev.end();
            self.prev = None;
            Some(prev.as_str())
        };
        self.idx += 1;
        r
    }
}

impl RegexSpit for Regex {
    fn split_inclusive_iter<'r, 't>(&'r self, text: &'t str) -> SplitInclusive<'r, 't> {
        SplitInclusive {
            finder: self.find_iter(text),
            prev: None,
            last: 0,
            text,
            idx: 0,
        }
    }
}
