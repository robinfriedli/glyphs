use crate::{Error, Location, Log, INTEGER_LIMIT};
use std::{fmt, mem};

#[derive(Clone, Debug, PartialEq)]
pub enum Tag {
    // keywords
    Class,
    Else,
    If,
    InstanceOf,
    New,
    Return,
    While,
    // operators
    And,
    Assign,
    Divide,
    Equal,
    Greater,
    GreaterEqual,
    Minus,
    Modulo,
    Not,
    Or,
    Plus,
    Less,
    LessEqual,
    Times,
    Unequal,
    // punctuation
    CloseBrace,
    CloseBracket,
    CloseParentthesis,
    Comma,
    OpenBrace,
    OpenBracket,
    OpenParenthesis,
    Period,
    Semicolon,
}

impl Tag {
    pub fn from_char(c: char) -> Option<Self> {
        match c {
            '-' => Some(Tag::Minus),
            '%' => Some(Tag::Modulo),
            '+' => Some(Tag::Plus),
            '*' => Some(Tag::Times),
            '{' => Some(Tag::OpenBrace),
            '}' => Some(Tag::CloseBrace),
            '[' => Some(Tag::OpenBracket),
            ']' => Some(Tag::CloseBracket),
            '(' => Some(Tag::OpenParenthesis),
            ')' => Some(Tag::CloseParentthesis),
            ',' => Some(Tag::Comma),
            '.' => Some(Tag::Period),
            ';' => Some(Tag::Semicolon),
            _ => None,
        }
    }

    pub fn from_keyword(keyword: &str) -> Option<Self> {
        match keyword {
            "class" => Some(Tag::Class),
            "else" => Some(Tag::Else),
            "if" => Some(Tag::If),
            "instanceof" => Some(Tag::InstanceOf),
            "new" => Some(Tag::New),
            "return" => Some(Tag::Return),
            "while" => Some(Tag::While),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub location: Location,
    pub parsed_token: ParsedToken,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.parsed_token, self.location)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum ParsedToken {
    IdentifierToken(String),
    IntegerToken(i32),
    StaticToken(Tag),
    StringToken(String),
}

impl fmt::Display for ParsedToken {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                ParsedToken::IdentifierToken(ref val) => format!("IDENTIFIER '{}'", val),
                ParsedToken::IntegerToken(val) => format!("INTEGER {}", val),
                ParsedToken::StaticToken(ref val) => format!("TOKEN {:?}", val),
                ParsedToken::StringToken(ref val) => format!("STRING '{}'", val),
            }
        )
    }
}

pub struct Lexer<'l> {
    source: Vec<char>,
    log: &'l mut Log,
    curr_pos: Option<usize>,
}

impl<'l> Lexer<'l> {
    pub fn new_for_string(source: String, log: &'l mut Log) -> Self {
        Lexer {
            source: source.chars().collect(),
            log,
            curr_pos: None,
        }
    }
}

impl Lexer<'_> {
    pub fn read_token_stream(mut self) -> Vec<Token> {
        let mut token_stream = Vec::new();
        let mut curr_state = State {
            conception_idx: 0,
            state_type: StateType::ScanningState,
        };

        while let Some((pos, c)) = self.read_next() {
            if !curr_state.is_literal_mode(c) {
                if let Some(special_type) = StateType::special_type_for_char(c) {
                    curr_state.terminate(pos.saturating_sub(1), &mut token_stream, self.log);
                    curr_state = State {
                        conception_idx: pos,
                        state_type: special_type,
                    };
                    continue;
                } else if char::is_whitespace(c) {
                    curr_state.terminate(pos.saturating_sub(1), &mut token_stream, self.log);
                    curr_state = State {
                        conception_idx: pos,
                        state_type: StateType::ScanningState,
                    };
                } else if let Some(tag) = Tag::from_char(c) {
                    curr_state.terminate(pos.saturating_sub(1), &mut token_stream, self.log);
                    token_stream.push(Token {
                        location: Location {
                            start: pos,
                            end: pos,
                        },
                        parsed_token: ParsedToken::StaticToken(tag),
                    });
                    curr_state = State {
                        conception_idx: pos + 1,
                        state_type: StateType::ScanningState,
                    };
                    continue;
                } else if c == '/' {
                    curr_state.terminate(pos.saturating_sub(1), &mut token_stream, self.log);
                    let prev_pos = pos;

                    if let Some((pos, c)) = self.read_next() {
                        if c == '*' || c == '/' {
                            curr_state = State {
                                conception_idx: prev_pos,
                                state_type: StateType::CommentState {
                                    is_block_comment: c == '*',
                                    prev_c: None,
                                },
                            };
                            continue;
                        } else {
                            token_stream.push(Token {
                                location: Location {
                                    start: prev_pos,
                                    end: prev_pos,
                                },
                                parsed_token: ParsedToken::StaticToken(Tag::Divide),
                            });
                            curr_state = State {
                                conception_idx: pos,
                                state_type: StateType::ScanningState,
                            };
                        }
                    } else {
                        self.log.errors.push(Error {
                            location: Location {
                                start: pos,
                                end: pos,
                            },
                            msg: String::from("Unexpected token"),
                        });
                        curr_state = State {
                            conception_idx: pos,
                            state_type: StateType::ScanningState,
                        };
                    }
                } else if !char::is_ascii_alphabetic(&c)
                    && !char::is_ascii_digit(&c)
                    && c != '"'
                    && c != '_'
                {
                    self.log.errors.push(Error {
                        location: Location {
                            start: pos,
                            end: pos,
                        },
                        msg: format!("Illegal char '{}'", c),
                    });
                }
            }

            curr_state = curr_state.handle_char(c, pos, &mut token_stream, self.log);
        }

        curr_state.terminate(
            self.curr_pos.map(|p| p.saturating_sub(1)).unwrap_or(0),
            &mut token_stream,
            self.log,
        );

        token_stream
    }

    fn read_next(&mut self) -> Option<(usize, char)> {
        let curr_pos = self.curr_pos.get_or_insert(0);
        let pos = *curr_pos;
        let res = self.source.get(*curr_pos);

        if res.is_some() {
            *curr_pos += 1;
        }

        res.map(|res| (pos, *res))
    }
}

struct State {
    conception_idx: usize,
    state_type: StateType,
}

#[allow(clippy::enum_variant_names)]
enum StateType {
    ScanningState,
    IdentifierState(String),
    IntegerState(String),
    StringState(String),
    CommentState {
        is_block_comment: bool,
        prev_c: Option<char>,
    },
    AndOrState {
        is_or: bool,
    },
    /// State for an assortment of operators that may be used in an equality check, e.g. ! for != or < for <= or = for == itself
    EqualityState {
        // tag if paired with equality operator
        equality_tag: Tag,
        // tag if single operator
        single_tag: Tag,
    },
}

impl State {
    /// Handle the given character in the current state and return the state used to handle the next char
    fn handle_char(
        mut self,
        c: char,
        pos: usize,
        token_stream: &mut Vec<Token>,
        log: &mut Log,
    ) -> Self {
        match self.state_type {
            StateType::ScanningState => {
                if char::is_ascii_digit(&c) {
                    return State {
                        conception_idx: pos,
                        state_type: StateType::IntegerState(String::new()),
                    }
                    .handle_char(c, pos, token_stream, log);
                } else if char::is_ascii_alphabetic(&c) {
                    return State {
                        conception_idx: pos,
                        state_type: StateType::IdentifierState(String::new()),
                    }
                    .handle_char(c, pos, token_stream, log);
                } else if c == '"' {
                    return State {
                        conception_idx: pos,
                        state_type: StateType::StringState(String::new()),
                    };
                }

                self
            }
            StateType::IdentifierState(ref mut val) => {
                if char::is_ascii_digit(&c) || char::is_ascii_alphabetic(&c) || c == '_' {
                    val.push(c);
                } else {
                    self.terminate(pos.saturating_sub(1), token_stream, log);
                    return State {
                        conception_idx: pos,
                        state_type: StateType::ScanningState,
                    }
                    .handle_char(c, pos, token_stream, log);
                }

                self
            }
            StateType::IntegerState(ref mut val) => {
                if char::is_ascii_digit(&c) {
                    val.push(c);
                } else {
                    self.terminate(pos.saturating_sub(1), token_stream, log);
                    return State {
                        conception_idx: pos,
                        state_type: StateType::ScanningState,
                    }
                    .handle_char(c, pos, token_stream, log);
                }

                self
            }
            StateType::StringState(ref mut val) => {
                if c == '"' {
                    token_stream.push(Token {
                        location: Location {
                            start: self.conception_idx,
                            end: pos,
                        },
                        // swap the String within this State for an unallocated empty String and move it to the Token
                        // instead of cloning as we do not need the State anymore to save memory allocation
                        parsed_token: ParsedToken::StringToken(mem::take(val)),
                    });

                    State {
                        conception_idx: pos + 1,
                        state_type: StateType::ScanningState,
                    }
                } else {
                    val.push(c);
                    self
                }
            }
            StateType::CommentState {
                is_block_comment,
                ref mut prev_c,
            } => {
                if is_block_comment && *prev_c == Some('*') && c == '/' {
                    return State {
                        conception_idx: pos + 1,
                        state_type: StateType::ScanningState,
                    };
                }
                *prev_c = Some(c);
                self
            }
            StateType::AndOrState { is_or } => {
                if is_or && c == '|' {
                    token_stream.push(Token {
                        location: Location {
                            start: self.conception_idx,
                            end: pos,
                        },
                        parsed_token: ParsedToken::StaticToken(Tag::Or),
                    });
                } else if !is_or && c == '&' {
                    token_stream.push(Token {
                        location: Location {
                            start: self.conception_idx,
                            end: pos,
                        },
                        parsed_token: ParsedToken::StaticToken(Tag::And),
                    });
                } else {
                    self.terminate(pos, token_stream, log);
                    return State {
                        conception_idx: pos,
                        state_type: StateType::ScanningState,
                    }
                    .handle_char(c, pos, token_stream, log);
                }

                State {
                    conception_idx: pos + 1,
                    state_type: StateType::ScanningState,
                }
            }
            StateType::EqualityState {
                ref equality_tag, ..
            } => {
                if c == '=' {
                    token_stream.push(Token {
                        location: Location {
                            start: self.conception_idx,
                            end: pos,
                        },
                        parsed_token: ParsedToken::StaticToken(Tag::clone(equality_tag)),
                    });

                    State {
                        conception_idx: pos + 1,
                        state_type: StateType::ScanningState,
                    }
                } else {
                    self.terminate(pos.saturating_sub(1), token_stream, log);
                    State {
                        conception_idx: pos,
                        state_type: StateType::ScanningState,
                    }
                    .handle_char(c, pos, token_stream, log)
                }
            }
        }
    }

    fn terminate(self, pos: usize, token_stream: &mut Vec<Token>, log: &mut Log) {
        match self.state_type {
            StateType::ScanningState => {}
            StateType::IdentifierState(val) => {
                let location = Location {
                    start: self.conception_idx,
                    end: pos,
                };
                if let Some(keyword_tag) = Tag::from_keyword(&val) {
                    token_stream.push(Token {
                        location,
                        parsed_token: ParsedToken::StaticToken(keyword_tag),
                    });
                } else {
                    token_stream.push(Token {
                        location,
                        parsed_token: ParsedToken::IdentifierToken(val),
                    });
                }
            }
            StateType::IntegerState(val) => {
                let location = Location {
                    start: self.conception_idx,
                    end: pos,
                };
                if let Ok(parsed_val) = val.parse::<u32>() {
                    if parsed_val > crate::INTEGER_LIMIT {
                        log.errors.push(Error {
                            location,
                            msg: format!(
                                "Integer literal {} exceeds maximum size of {}",
                                parsed_val,
                                crate::INTEGER_LIMIT
                            ),
                        });
                    } else if parsed_val == INTEGER_LIMIT {
                        // The integer literal token usually stores the value unsigned, but for the minimal integer value this is not
                        // possible, since the absolute value of the minmal value is one higher than the absolute value of the maximum
                        // value (-2147483648 vs. 2147483647), so the minimal value has to be handled separately.
                        //
                        // Here, if the literal was 2147483648 it will simply be stored as Integer.MIN_VALUE, whether the previous token
                        // was a minus (-) and the literal is valid is checked by the parser.
                        token_stream.push(Token {
                            location,
                            parsed_token: ParsedToken::IntegerToken(i32::MIN),
                        });
                    } else {
                        token_stream.push(Token {
                            location,
                            parsed_token: ParsedToken::IntegerToken(parsed_val as i32),
                        });
                    }
                } else {
                    log.errors.push(Error {
                        location,
                        msg: format!("Invalid integer literal '{}'", val),
                    });
                }
            }
            StateType::StringState(_) => log.errors.push(Error {
                location: Location {
                    start: self.conception_idx,
                    end: pos,
                },
                msg: String::from("Unclosed String literal"),
            }),
            StateType::CommentState {
                is_block_comment, ..
            } if is_block_comment => log.errors.push(Error {
                location: Location {
                    start: self.conception_idx,
                    end: pos,
                },
                msg: String::from("Unclosed block comment"),
            }),
            StateType::CommentState { .. } => {}
            // TODO allow
            StateType::AndOrState { is_or } => log.errors.push(Error {
                location: Location {
                    start: self.conception_idx,
                    end: pos,
                },
                msg: format!("Single '{}' not allowed", if is_or { '|' } else { '&' }),
            }),
            StateType::EqualityState { single_tag, .. } => token_stream.push(Token {
                location: Location {
                    start: self.conception_idx,
                    end: pos,
                },
                parsed_token: ParsedToken::StaticToken(single_tag),
            }),
        }
    }

    /// Determine whether the state accepts a special char that would normally cause a state switch, used for comments and string literals,
    /// or for tokens consisting of two special tokens, e.g. != or &&
    fn is_literal_mode(&self, c: char) -> bool {
        match self.state_type {
            StateType::ScanningState => false,
            StateType::IdentifierState(_) => false,
            StateType::IntegerState(_) => false,
            StateType::StringState(_) => c != '\n' && c != '\r',
            StateType::CommentState {
                is_block_comment, ..
            } => is_block_comment || (c != '\n' && c != '\r'),
            StateType::AndOrState { is_or } => (is_or && c == '|') || (!is_or && c == '&'),
            StateType::EqualityState { .. } => c == '=',
        }
    }
}

impl StateType {
    fn special_type_for_char(c: char) -> Option<Self> {
        match c {
            '&' => Some(StateType::AndOrState { is_or: false }),
            '|' => Some(StateType::AndOrState { is_or: true }),
            '=' => Some(StateType::EqualityState {
                equality_tag: Tag::Equal,
                single_tag: Tag::Assign,
            }),
            '!' => Some(StateType::EqualityState {
                equality_tag: Tag::Unequal,
                single_tag: Tag::Not,
            }),
            '<' => Some(StateType::EqualityState {
                equality_tag: Tag::LessEqual,
                single_tag: Tag::Less,
            }),
            '>' => Some(StateType::EqualityState {
                equality_tag: Tag::GreaterEqual,
                single_tag: Tag::Greater,
            }),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::{
        lexer::{Lexer, ParsedToken, ParsedToken::*, Tag, Token},
        Location, Log,
    };

    #[test]
    fn test_empty_source() {
        let mut log = Log { errors: Vec::new() };

        let lexer = Lexer::new_for_string(String::new(), &mut log);
        let token_stream = lexer.read_token_stream();
        assert!(token_stream.is_empty());
        assert!(log.errors.is_empty());
    }

    #[test]
    fn test_block_comment() {
        let mut log = Log { errors: Vec::new() };

        let lexer = Lexer::new_for_string(String::from("class /* Comment */ A { }"), &mut log);
        let mut token_stream = lexer.read_token_stream().into_iter();
        assert!(log.errors.is_empty());
        assert_token(token_stream.next(), 0, 4, StaticToken(Tag::Class));
        assert_token(
            token_stream.next(),
            20,
            20,
            IdentifierToken(String::from("A")),
        );
        assert_token(token_stream.next(), 22, 22, StaticToken(Tag::OpenBrace));
        assert_token(token_stream.next(), 24, 24, StaticToken(Tag::CloseBrace));
        assert_eq!(token_stream.next(), None);
    }

    #[test]
    fn test_line_comment() {
        let mut log = Log { errors: Vec::new() };

        let lexer = Lexer::new_for_string(String::from("class // Comment \r\nA { }"), &mut log);
        let mut token_stream = lexer.read_token_stream().into_iter();
        assert!(log.errors.is_empty());
        assert_token(token_stream.next(), 0, 4, StaticToken(Tag::Class));
        assert_token(
            token_stream.next(),
            19,
            19,
            IdentifierToken(String::from("A")),
        );
        assert_token(token_stream.next(), 21, 21, StaticToken(Tag::OpenBrace));
        assert_token(token_stream.next(), 23, 23, StaticToken(Tag::CloseBrace));
        assert_eq!(token_stream.next(), None);
    }

    #[test]
    fn test_keywords() {
        let mut log = Log { errors: Vec::new() };

        let lexer = Lexer::new_for_string(
            String::from("class else  if instanceof new return while"),
            &mut log,
        );
        let mut token_stream = lexer.read_token_stream().into_iter();
        assert!(log.errors.is_empty());

        assert_token(token_stream.next(), 0, 4, StaticToken(Tag::Class));
        assert_token(token_stream.next(), 6, 9, StaticToken(Tag::Else));
        assert_token(token_stream.next(), 12, 13, StaticToken(Tag::If));
        assert_token(token_stream.next(), 15, 24, StaticToken(Tag::InstanceOf));
        assert_token(token_stream.next(), 26, 28, StaticToken(Tag::New));
        assert_token(token_stream.next(), 30, 35, StaticToken(Tag::Return));
        assert_token(token_stream.next(), 37, 41, StaticToken(Tag::While));

        assert_eq!(token_stream.next(), None);
    }

    #[test]
    fn test_operators() {
        let mut log = Log { errors: Vec::new() };

        let lexer = Lexer::new_for_string(
            String::from("&& = / == != > >= - % ! || + < <= *"),
            &mut log,
        );
        let mut token_stream = lexer.read_token_stream().into_iter();
        assert!(log.errors.is_empty());

        assert_token(token_stream.next(), 0, 1, StaticToken(Tag::And));
        assert_token(token_stream.next(), 3, 3, StaticToken(Tag::Assign));
        assert_token(token_stream.next(), 5, 5, StaticToken(Tag::Divide));
        assert_token(token_stream.next(), 7, 8, StaticToken(Tag::Equal));
        assert_token(token_stream.next(), 10, 11, StaticToken(Tag::Unequal));
        assert_token(token_stream.next(), 13, 13, StaticToken(Tag::Greater));
        assert_token(token_stream.next(), 15, 16, StaticToken(Tag::GreaterEqual));
        assert_token(token_stream.next(), 18, 18, StaticToken(Tag::Minus));
        assert_token(token_stream.next(), 20, 20, StaticToken(Tag::Modulo));
        assert_token(token_stream.next(), 22, 22, StaticToken(Tag::Not));
        assert_token(token_stream.next(), 24, 25, StaticToken(Tag::Or));
        assert_token(token_stream.next(), 27, 27, StaticToken(Tag::Plus));
        assert_token(token_stream.next(), 29, 29, StaticToken(Tag::Less));
        assert_token(token_stream.next(), 31, 32, StaticToken(Tag::LessEqual));
        assert_token(token_stream.next(), 34, 34, StaticToken(Tag::Times));

        assert_eq!(token_stream.next(), None);
    }

    #[test]
    fn test_punctuation() {
        let mut log = Log { errors: Vec::new() };

        let lexer = Lexer::new_for_string(String::from("{}[](),.;"), &mut log);
        let mut token_stream = lexer.read_token_stream().into_iter();
        assert!(log.errors.is_empty());

        assert_token(token_stream.next(), 0, 0, StaticToken(Tag::OpenBrace));
        assert_token(token_stream.next(), 1, 1, StaticToken(Tag::CloseBrace));
        assert_token(token_stream.next(), 2, 2, StaticToken(Tag::OpenBracket));
        assert_token(token_stream.next(), 3, 3, StaticToken(Tag::CloseBracket));
        assert_token(token_stream.next(), 4, 4, StaticToken(Tag::OpenParenthesis));
        assert_token(
            token_stream.next(),
            5,
            5,
            StaticToken(Tag::CloseParentthesis),
        );
        assert_token(token_stream.next(), 6, 6, StaticToken(Tag::Comma));
        assert_token(token_stream.next(), 7, 7, StaticToken(Tag::Period));
        assert_token(token_stream.next(), 8, 8, StaticToken(Tag::Semicolon));

        assert_eq!(token_stream.next(), None);
    }

    #[test]
    fn test_value_tokens() {
        let mut log = Log { errors: Vec::new() };

        let lexer = Lexer::new_for_string(String::from("123 45\"ABC!\"12abc34"), &mut log);
        let mut token_stream = lexer.read_token_stream().into_iter();
        assert!(log.errors.is_empty());

        assert_token(token_stream.next(), 0, 2, IntegerToken(123));
        assert_token(token_stream.next(), 4, 5, IntegerToken(45));
        assert_token(
            token_stream.next(),
            6,
            11,
            StringToken(String::from("ABC!")),
        );
        assert_token(token_stream.next(), 12, 13, IntegerToken(12));
        assert_token(
            token_stream.next(),
            14,
            18,
            IdentifierToken(String::from("abc34")),
        );

        assert_eq!(token_stream.next(), None);
    }

    #[test]
    fn test_single_line_comment() {
        let mut log = Log { errors: Vec::new() };

        let lexer = Lexer::new_for_string(
            String::from("// some * comment {}$980 /* dfwe * *7f /*/\r\nx = 7"),
            &mut log,
        );
        let mut token_stream = lexer.read_token_stream().into_iter();
        assert!(log.errors.is_empty());

        assert_token(
            token_stream.next(),
            44,
            44,
            IdentifierToken(String::from("x")),
        );
        assert_token(token_stream.next(), 46, 46, StaticToken(Tag::Assign));
        assert_token(token_stream.next(), 48, 48, IntegerToken(7));

        assert_eq!(token_stream.next(), None);
    }

    #[inline]
    fn assert_token(
        actual_token: Option<Token>,
        expected_start: usize,
        expected_end: usize,
        expected_parsed_token: ParsedToken,
    ) {
        assert_eq!(
            actual_token,
            Some(Token {
                location: Location {
                    start: expected_start,
                    end: expected_end
                },
                parsed_token: expected_parsed_token
            })
        );
    }
}
