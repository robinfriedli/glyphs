use std::{iter::Peekable, mem, vec::IntoIter};

use crate::{
    lexer::{ParsedToken, Tag, Token},
    Error, Location, Log,
};

use self::ast::*;

pub mod ast;
pub mod visitor;

pub static ERROR_IDENTIFIER: &str = "$ERROR$";

pub struct Parser<'l> {
    token_stream: Peekable<IntoIter<Token>>,
    log: &'l mut Log,
    curr_tok: Option<Token>,
    prev_end: usize,
    current_start: usize,
}

impl<'l> Parser<'l> {
    pub fn new(token_stream: Vec<Token>, log: &'l mut Log) -> Self {
        Parser {
            token_stream: token_stream.into_iter().peekable(),
            log,
            curr_tok: None,
            prev_end: 0,
            current_start: 0,
        }
    }
}

impl Parser<'_> {
    pub fn parse_program(mut self) -> Result<Node<ProgramNode>, ParserError> {
        let mut classes = Vec::new();
        let start = self.current_start;

        if self.advance() {
            while !self.is_end() {
                classes.push(self.parse_class()?);
            }
        }

        self.advance();
        let location = Location {
            start,
            end: self.prev_end,
        };

        Ok(Node {
            location,
            node_type: ProgramNode { classes },
        })
    }

    fn parse_class(&mut self) -> Result<Node<ClassNode>, ParserError> {
        let start = self.current_start;
        self.check_curr_tag(&Tag::Class);

        let identifier = self.read_identifier()?;
        let base_class;
        let mut field_nodes = Vec::new();
        let mut method_nodes = Vec::new();

        if self.curr_is_tag(&Tag::Extends) {
            self.next()?;
            let base_class_start = self.current_start;
            let base_class_ident = self.read_identifier()?;
            base_class = Some(Node {
                location: Location {
                    start: base_class_start,
                    end: self.prev_end,
                },
                node_type: BasicTypeNode {
                    identifier: base_class_ident,
                },
            });
            self.check_curr_tag(&Tag::OpenBrace);
        } else if self.curr_is_tag(&Tag::OpenBrace) {
            base_class = None;
            if !self.is_end() {
                self.next().unwrap();
            }
        } else if self.curr_tok.is_some() {
            self.report_error(format!(
                "Unexpected token in class declaration: {}",
                &self.curr_tok.as_ref().unwrap()
            ));
            base_class = None;
        } else {
            return Err(ParserError::PrematureEof);
        }

        while !self.is_end() && !self.curr_is_tag(&Tag::CloseBrace) {
            let field_or_return_type_start = self.current_start;
            let field_or_return_type = self.read_type_node()?;
            let field_or_method_identifier = self.read_identifier()?;

            if self.curr_is_tag(&Tag::OpenParenthesis) {
                let mut parameters = Vec::new();
                self.next()?;

                if !self.curr_is_tag(&Tag::CloseParentthesis) {
                    loop {
                        let current_param_start = self.current_start;
                        let param_type = self.read_type_node()?;
                        let param_ident = self.read_identifier()?;
                        let param_location = Location {
                            start: current_param_start,
                            end: self.prev_end,
                        };
                        parameters.push(Node {
                            location: param_location,
                            node_type: VariableNode {
                                var_type: param_type,
                                identifier: param_ident,
                            },
                        });

                        if !self.curr_is_tag(&Tag::Comma) {
                            break;
                        }

                        if !self.advance() {
                            break;
                        }
                    }
                }

                self.check_curr_tag(&Tag::CloseParentthesis);
                let statement_block_node = self.parse_statement_block()?;

                method_nodes.push(Node {
                    location: Location {
                        start: field_or_return_type_start,
                        end: self.prev_end,
                    },
                    node_type: MethodNode {
                        return_type: field_or_return_type,
                        identifier: field_or_method_identifier,
                        parameters,
                        body: statement_block_node,
                    },
                });

                continue;
            } else if self.curr_is_tag(&Tag::Semicolon) {
                field_nodes.push(Node {
                    location: Location {
                        start: field_or_return_type_start,
                        end: self.prev_end,
                    },
                    node_type: VariableNode {
                        var_type: field_or_return_type,
                        identifier: field_or_method_identifier,
                    },
                });
            } else {
                self.report_error(format!("Unexpected token while parsing method or variable, expected {:?} or {:?} but got: {:?}", Tag::OpenParenthesis, Tag::Semicolon, &self.curr_tok));
            }

            self.advance();
        }

        if !self.curr_is_tag(&Tag::CloseBrace) {
            self.report_error(String::from("Unclosed class declaration"));
        }

        self.advance();

        Ok(Node {
            location: Location {
                start,
                end: self.prev_end,
            },
            node_type: ClassNode {
                identifier,
                base_class,
                fields: field_nodes,
                methods: method_nodes,
            },
        })
    }

    fn parse_statement_block(&mut self) -> Result<Node<StatementBlockNode>, ParserError> {
        let statement_block_start = self.current_start;
        let mut statements: Vec<Box<Node<dyn StatementNode>>> = Vec::new();
        self.check_curr_tag(&Tag::OpenBrace);

        while !(self.is_end() || self.curr_is_tag(&Tag::CloseBrace)) {
            if self.curr_is_tag(&Tag::Semicolon) {
                self.advance();
            } else if self.curr_is_tag(&Tag::If) {
                let if_statement_block_start = self.current_start;
                self.next()?;
                self.check_curr_tag(&Tag::OpenParenthesis);
                let if_expression = self.parse_expression()?;
                self.check_curr_tag(&Tag::CloseParentthesis);
                let then_block = self.parse_statement_block()?;
                let else_block = if self.curr_is_tag(&Tag::Else) {
                    self.next()?;
                    Some(self.parse_statement_block()?)
                } else {
                    None
                };

                statements.push(Box::new(Node {
                    location: Location {
                        start: if_statement_block_start,
                        end: self.prev_end,
                    },
                    node_type: IfStatementNode {
                        condition: if_expression,
                        then_block,
                        else_block,
                    },
                }));
            } else if self.curr_is_tag(&Tag::While) {
                let while_statement_start = self.current_start;
                self.next()?;
                self.check_curr_tag(&Tag::OpenParenthesis);
                let while_expression = self.parse_expression()?;
                self.check_curr_tag(&Tag::CloseParentthesis);
                let while_block = self.parse_statement_block()?;
                statements.push(Box::new(Node {
                    location: Location {
                        start: while_statement_start,
                        end: self.prev_end,
                    },
                    node_type: WhileStatementNode {
                        condition: while_expression,
                        body: while_block,
                    },
                }));
            } else if self.curr_is_tag(&Tag::Return) {
                let return_statement_start = self.current_start;
                self.next()?;

                let return_expression = if self.curr_is_tag(&Tag::Semicolon) {
                    None
                } else {
                    Some(self.parse_expression()?)
                };

                statements.push(Box::new(Node {
                    location: Location {
                        start: return_statement_start,
                        end: self.prev_end,
                    },
                    node_type: ReturnStatementNode {
                        expression: return_expression,
                    },
                }));
            } else if let Some(Token {
                parsed_token: ParsedToken::IdentifierToken(_),
                ..
            }) = self.curr_tok
            {
                self.handle_non_static_statement(&mut statements)?;
            } else {
                self.report_error(format!("Unexpected token: {:?}", &self.curr_tok));
                self.advance();
            }
        }

        if !self.curr_is_tag(&Tag::CloseBrace) {
            self.report_error(format!(
                "Expected: {:?}, but got: {:?}",
                Tag::CloseBrace,
                &self.curr_tok
            ));
        }

        self.next()?;

        Ok(Node {
            location: Location {
                start: statement_block_start,
                end: self.prev_end,
            },
            node_type: StatementBlockNode { statements },
        })
    }

    fn handle_non_static_statement(
        &mut self,
        statements: &mut Vec<Box<Node<dyn StatementNode>>>,
    ) -> Result<(), ParserError> {
        let start = self.current_start;
        let identifier = self.read_identifier()?;
        let identifier_end = self.prev_end;
        let mut designator_node: Option<Box<Node<dyn DesignatorNode>>> = None;

        if self.curr_is_tag(&Tag::OpenBracket) {
            self.next()?;

            // is variable with array type, e.g. int[] x;
            if self.curr_is_tag(&Tag::CloseBracket) {
                self.next()?;

                let mut type_node: Box<Node<dyn TypeNode>> = Box::new(Node {
                    location: Location {
                        start,
                        end: self.prev_end,
                    },
                    node_type: ArrayTypeNode {
                        element_type: Box::new(Node {
                            location: Location {
                                start,
                                end: identifier_end,
                            },
                            node_type: BasicTypeNode { identifier },
                        }),
                    },
                });
                type_node = self.handle_array_type(start, type_node)?;

                let variable_identifier = self.read_identifier()?;
                statements.push(Box::new(Node {
                    location: Location {
                        start,
                        end: self.prev_end,
                    },
                    node_type: LocalDeclarationNode {
                        variable: Node {
                            location: Location {
                                start,
                                end: self.prev_end,
                            },
                            node_type: VariableNode {
                                var_type: type_node,
                                identifier: variable_identifier,
                            },
                        },
                    },
                }));

                self.check_curr_tag(&Tag::Semicolon);
                return Ok(());
            } else {
                // is assignment with element access, e.g. x[0] = 3;
                let element_access_expression = self.parse_expression()?;
                self.check_curr_tag(&Tag::CloseBracket);

                designator_node = Some(Box::new(Node {
                    location: Location {
                        start,
                        end: self.prev_end,
                    },
                    node_type: ElementAccessNode {
                        designator: Box::new(Node {
                            location: Location {
                                start,
                                end: identifier_end,
                            },
                            node_type: BasicDesignatorNode {
                                identifier: identifier.clone(),
                            },
                        }),
                        expression: element_access_expression,
                    },
                }));
            }
        } else if let Some(Token {
            parsed_token: ParsedToken::IdentifierToken(_),
            ..
        }) = self.curr_tok
        {
            // is simple variable, e.g. int x;
            let type_node: Box<Node<dyn TypeNode>> = Box::new(Node {
                location: Location {
                    start,
                    end: identifier_end,
                },
                node_type: BasicTypeNode { identifier },
            });

            let variable_identifier = self.read_identifier()?;
            statements.push(Box::new(Node {
                location: Location {
                    start,
                    end: self.prev_end,
                },
                node_type: LocalDeclarationNode {
                    variable: Node {
                        location: Location {
                            start,
                            end: self.prev_end,
                        },
                        node_type: VariableNode {
                            var_type: type_node,
                            identifier: variable_identifier,
                        },
                    },
                },
            }));

            self.check_curr_tag(&Tag::Semicolon);
            return Ok(());
        }

        let final_designator_node = if let Some(left) = designator_node {
            // it has been determined that it is not a TypeNode but a DesignatorNode with element access, parse full DesignatorNode with
            // its current part as left designator
            self.parse_designator_from_pos(start, left)?
        } else {
            self.parse_designator_from_pos(
                start,
                Box::new(Node {
                    location: Location {
                        start,
                        end: identifier_end,
                    },
                    node_type: BasicDesignatorNode { identifier },
                }),
            )?
        };

        if self.curr_is_tag(&Tag::Assign) {
            self.next()?;
            let expression = self.parse_expression()?;
            statements.push(Box::new(Node {
                location: Location {
                    start,
                    end: self.prev_end,
                },
                node_type: AssignmentNode {
                    left: final_designator_node,
                    right: expression,
                },
            }));
            self.check_curr_tag(&Tag::Semicolon);
        } else if self.curr_is_tag(&Tag::OpenParenthesis) {
            let method_call_node = self.parse_method_call(start, final_designator_node)?;
            statements.push(Box::new(Node {
                location: Location {
                    start,
                    end: self.prev_end,
                },
                node_type: CallStatementNode {
                    call: method_call_node,
                },
            }));
            self.check_curr_tag(&Tag::Semicolon);
        } else {
            self.report_error(format!(
                "Unexpected token after designator, expected = or ( but got: {:?}",
                &self.curr_tok
            ));
            self.advance();
        }

        Ok(())
    }

    fn parse_expression(&mut self) -> Result<Box<Node<dyn ExpressionNode>>, ParserError> {
        let start = self.current_start;
        let mut left = self.parse_logic_term()?;

        while self.curr_is_tag(&Tag::Or) {
            self.next()?;
            let right = self.parse_logic_term()?;
            let location = Location {
                start,
                end: self.prev_end,
            };
            left = Box::new(Node {
                location,
                node_type: BinaryExpressionNode {
                    left,
                    op: Operator::Or,
                    right,
                },
            });
        }

        Ok(left)
    }

    fn parse_simple_expression(&mut self) -> Result<Box<Node<dyn ExpressionNode>>, ParserError> {
        let start = self.current_start;
        let mut left = self.parse_term()?;

        while let Some(op) = self.read_operator(|tag| Operator::for_simple_math_operator_tag(tag)) {
            self.next()?;
            let right = self.parse_term()?;
            let location = Location {
                start,
                end: self.prev_end,
            };
            left = Box::new(Node {
                location,
                node_type: BinaryExpressionNode { left, op, right },
            });
        }

        Ok(left)
    }

    fn parse_term(&mut self) -> Result<Box<Node<dyn ExpressionNode>>, ParserError> {
        let start = self.current_start;
        let mut left = self.parse_factor()?;

        while let Some(op) = self.read_operator(|tag| Operator::for_math_term_operator_tag(tag)) {
            self.next()?;
            let right = self.parse_factor()?;
            let location = Location {
                start,
                end: self.prev_end,
            };
            left = Box::new(Node {
                location,
                node_type: BinaryExpressionNode { left, op, right },
            });
        }

        Ok(left)
    }

    fn parse_logic_term(&mut self) -> Result<Box<Node<dyn ExpressionNode>>, ParserError> {
        let start = self.current_start;
        let mut left = self.parse_logic_factor()?;

        while self.curr_is_tag(&Tag::And) {
            self.next()?;
            let right = self.parse_logic_factor()?;
            let location = Location {
                start,
                end: self.prev_end,
            };
            left = Box::new(Node {
                location,
                node_type: BinaryExpressionNode {
                    left,
                    op: Operator::And,
                    right,
                },
            });
        }

        Ok(left)
    }

    fn parse_factor(&mut self) -> Result<Box<Node<dyn ExpressionNode>>, ParserError> {
        let start = self.current_start;

        if let Some(operator) = self.read_operator(|tag| Operator::for_unary_operator_tag(tag)) {
            self.next()?;
            self.parse_unary_expression(start, operator)
        } else if self.curr_is_tag(&Tag::OpenParenthesis) {
            self.next()?;
            let expression = self.parse_expression()?;
            self.check_curr_tag(&Tag::CloseParentthesis);

            if let Some(Token {
                parsed_token: ParsedToken::IdentifierToken(_),
                ..
            }) = self.curr_tok
            {
                // TODO maybe change syntax from `(Type) var` to `var as Type`
                self.parse_type_cast(start, expression).map(|res| {
                    let node: Box<Node<dyn ExpressionNode>> = Box::new(res);
                    node
                })
            } else {
                Ok(expression)
            }
        } else {
            self.parse_operand()
        }
    }

    fn parse_operand(&mut self) -> Result<Box<Node<dyn ExpressionNode>>, ParserError> {
        let start = self.current_start;
        match self.curr_tok {
            Some(Token {
                parsed_token: ParsedToken::IntegerToken(val),
                ..
            }) => {
                self.validate_int_bounds(val, false);
                self.next()?;
                Ok(Box::new(Node {
                    location: Location {
                        start,
                        end: self.prev_end,
                    },
                    node_type: IntegerLiteralNode { val },
                }))
            }
            Some(Token {
                parsed_token: ParsedToken::StringToken(ref mut val),
                ..
            }) => {
                let val = mem::take(val);
                self.next()?;
                Ok(Box::new(Node {
                    location: Location {
                        start,
                        end: self.prev_end,
                    },
                    node_type: StringLiteralNode { val },
                }))
            }
            _ => {
                if self.curr_is_tag(&Tag::New) {
                    self.parse_creation()
                } else {
                    let mut designator = self.parse_designator()?;
                    if self.curr_is_tag(&Tag::OpenParenthesis) {
                        self.parse_method_call(start, designator).map(|res| {
                            let node: Box<Node<dyn ExpressionNode>> = Box::new(res);
                            node
                        })
                    } else {
                        // TODO use upcasting coercion when it becomes stable https://github.com/rust-lang/rust/issues/65991
                        Ok(designator
                            .node_type
                            .move_into_expression_node(designator.location))
                    }
                }
            }
        }
    }

    fn parse_method_call(
        &mut self,
        start: usize,
        designator: Box<Node<dyn DesignatorNode>>,
    ) -> Result<Node<MethodCallNode>, ParserError> {
        let mut arguments = Vec::new();
        self.check_curr_tag(&Tag::OpenParenthesis);

        if !self.curr_is_tag(&Tag::CloseParentthesis) {
            arguments.push(self.parse_expression()?);
            while self.curr_is_tag(&Tag::Comma) {
                self.next()?;
                arguments.push(self.parse_expression()?);
            }
        }

        self.check_curr_tag(&Tag::CloseParentthesis);
        Ok(Node {
            location: Location {
                start,
                end: self.prev_end,
            },
            node_type: MethodCallNode {
                designator,
                arguments,
            },
        })
    }

    fn parse_creation(&mut self) -> Result<Box<Node<dyn ExpressionNode>>, ParserError> {
        let start = self.current_start;
        self.check_curr_tag(&Tag::New);
        let identifier_start = self.current_start;
        let identifier = self.read_identifier()?;
        let identifier_location = Location {
            start: identifier_start,
            end: self.prev_end,
        };
        let type_node = Node {
            location: identifier_location,
            node_type: BasicTypeNode { identifier },
        };

        if self.curr_is_tag(&Tag::OpenParenthesis) {
            self.next()?;
            // TODO support constructor params
            self.check_curr_tag(&Tag::CloseParentthesis);

            Ok(Box::new(Node {
                location: Location {
                    start,
                    end: self.prev_end,
                },
                node_type: ObjectCreationNode {
                    object_type: type_node,
                },
            }))
        } else {
            self.check_curr_tag(&Tag::OpenBracket);
            let expression = self.parse_expression()?;
            self.check_curr_tag(&Tag::CloseBracket);

            Ok(Box::new(Node {
                location: Location {
                    start,
                    end: self.prev_end,
                },
                node_type: ArrayCreationNode {
                    element_type: Box::new(type_node),
                    expression,
                },
            }))
        }
    }

    fn parse_type_cast(
        &mut self,
        start: usize,
        expression: Box<Node<dyn ExpressionNode>>,
    ) -> Result<Node<TypeCastNode>, ParserError> {
        let designator = self.parse_designator()?;
        let location = Location {
            start,
            end: self.prev_end,
        };
        let identifier = if let Some(basic_designator_node) =
            expression.node_type.unwrap_basic_designator_node()
        {
            basic_designator_node.identifier.clone()
        } else {
            self.report_error(format!("Invalid type {:?} in type cast", &expression));
            String::from(ERROR_IDENTIFIER)
        };

        let type_node = Node {
            location: expression.location.clone(),
            node_type: BasicTypeNode { identifier },
        };
        Ok(Node {
            location,
            node_type: TypeCastNode {
                type_node,
                designator,
            },
        })
    }

    fn parse_designator(&mut self) -> Result<Box<Node<dyn DesignatorNode>>, ParserError> {
        let start = self.current_start;
        let identifier = self.read_identifier()?;
        let location = Location {
            start,
            end: self.prev_end,
        };
        let left = Box::new(Node {
            location,
            node_type: BasicDesignatorNode { identifier },
        });
        self.parse_designator_from_pos(start, left)
    }

    fn parse_designator_from_pos(
        &mut self,
        start: usize,
        mut left: Box<Node<dyn DesignatorNode>>,
    ) -> Result<Box<Node<dyn DesignatorNode>>, ParserError> {
        while self.curr_is_tag(&Tag::Period) || self.curr_is_tag(&Tag::OpenBracket) {
            if self.curr_is_tag(&Tag::Period) {
                self.next()?;
                let identifier = self.read_identifier()?;
                let location = Location {
                    start,
                    end: self.prev_end,
                };
                left = Box::new(Node {
                    location,
                    node_type: MemberAccessNode {
                        designator: left,
                        identifier,
                    },
                });
            } else {
                self.check_curr_tag(&Tag::OpenBracket);
                let expression = self.parse_expression()?;
                self.check_curr_tag(&Tag::CloseBracket);
                let location = Location {
                    start,
                    end: self.prev_end,
                };
                left = Box::new(Node {
                    location,
                    node_type: ElementAccessNode {
                        designator: left,
                        expression,
                    },
                });
            }
        }

        Ok(left)
    }

    fn parse_logic_factor(&mut self) -> Result<Box<Node<dyn ExpressionNode>>, ParserError> {
        let start = self.current_start;
        let mut left = self.parse_simple_expression()?;

        while let Some(op) = self.read_operator(|tag| Operator::for_compare_operator_tag(tag)) {
            self.next()?;
            let right = self.parse_simple_expression()?;
            let location = Location {
                start,
                end: self.prev_end,
            };
            left = Box::new(Node {
                location,
                node_type: BinaryExpressionNode { left, op, right },
            });
        }

        Ok(left)
    }

    fn parse_unary_expression(
        &mut self,
        start: usize,
        operator: Operator,
    ) -> Result<Box<Node<dyn ExpressionNode>>, ParserError> {
        if let Some(Token {
            parsed_token: ParsedToken::IntegerToken(val),
            ..
        }) = self.curr_tok
        {
            if operator == Operator::Minus {
                self.validate_int_bounds(val, true);
                self.next()?;
                return Ok(Box::new(Node {
                    location: Location {
                        start,
                        end: self.prev_end,
                    },
                    node_type: IntegerLiteralNode {
                        val: if val == i32::MIN { i32::MIN } else { -val },
                    },
                }));
            }
        }

        let operand = self.parse_factor()?;
        let location = Location {
            start,
            end: self.prev_end,
        };
        Ok(Box::new(Node {
            location,
            node_type: UnaryExpressionNode {
                op: operator,
                operand,
            },
        }))
    }

    /// Check that using the literal 2147483648 is only allowed when negative, in which case allow_min_val is true.
    #[inline]
    fn validate_int_bounds(&mut self, val: i32, allow_min_val: bool) {
        if !allow_min_val && val == i32::MIN {
            self.report_error(format!("Integer literal exceeds bound of {}", i32::MAX));
        }
    }

    fn read_operator<F: FnOnce(&Tag) -> Option<Operator>>(
        &self,
        mapping_fn: F,
    ) -> Option<Operator> {
        match self.curr_tok {
            Some(Token {
                parsed_token: ParsedToken::StaticToken(ref tag),
                ..
            }) => mapping_fn(tag),
            _ => None,
        }
    }

    fn read_type_node(&mut self) -> Result<Box<Node<dyn TypeNode>>, ParserError> {
        let start = self.current_start;
        let identifier = self.read_identifier()?;
        let location = Location {
            start,
            end: self.prev_end,
        };
        let mut type_node: Box<Node<dyn TypeNode>> = Box::new(Node {
            location,
            node_type: BasicTypeNode { identifier },
        });
        type_node = self.handle_array_type(start, type_node)?;
        Ok(type_node)
    }

    fn handle_array_type(
        &mut self,
        start: usize,
        mut type_node: Box<Node<dyn TypeNode>>,
    ) -> Result<Box<Node<dyn TypeNode>>, ParserError> {
        // loop for multi dimensional arrays
        while self.curr_is_tag(&Tag::OpenBracket) {
            if !self.is_end() {
                self.next()?;
                while !self.curr_is_tag(&Tag::CloseBracket) && !self.is_end() {
                    self.report_error(format!(
                        "Unexpected token: {:?}. Expected: {:?}.",
                        &self.curr_tok,
                        Tag::CloseBracket
                    ));
                    self.next()?;
                }
            }

            if self.curr_is_tag(&Tag::CloseBracket) {
                let bracket_end = if !self.is_end() {
                    self.next()?;
                    self.prev_end
                } else {
                    self.curr_tok.as_ref().unwrap().location.end
                };

                let expanded_location = Location {
                    start,
                    end: bracket_end,
                };
                type_node = Box::new(Node {
                    location: expanded_location,
                    node_type: ArrayTypeNode {
                        element_type: type_node,
                    },
                });
            } else {
                self.report_error(String::from("Unclosed open bracket"));
                break;
            }
        }

        Ok(type_node)
    }

    fn read_identifier(&mut self) -> Result<String, ParserError> {
        match self.curr_tok {
            Some(Token {
                parsed_token: ParsedToken::IdentifierToken(ref mut ident),
                ..
            }) => {
                let val = mem::take(ident);
                self.next().map(|_| val)
            }
            _ => {
                self.report_error(String::from("Expected identifier"));
                self.next().map(|_| String::from(ERROR_IDENTIFIER))
            }
        }
    }

    fn report_error(&mut self, msg: String) {
        self.log.errors.push(Error {
            location: self
                .curr_tok
                .as_ref()
                .map(|tok| tok.location.clone())
                .unwrap_or_default(),
            msg,
        });
    }

    fn check_curr_tag(&mut self, tag: &Tag) {
        if !self.curr_is_tag(tag) {
            self.report_error(format!(
                "Expected static token for tag {:?} but got {:?}",
                tag, self.curr_tok
            ));
        }
        if !self.is_end() {
            self.next().unwrap();
        }
    }

    fn curr_is_tag(&self, tag: &Tag) -> bool {
        match self.curr_tok {
            Some(Token {
                parsed_token: ParsedToken::StaticToken(ref t),
                ..
            }) => *t == *tag,
            _ => false,
        }
    }

    fn is_end(&mut self) -> bool {
        self.token_stream.peek().is_none()
    }

    fn advance(&mut self) -> bool {
        if let Some(ref curr_tok) = self.curr_tok {
            self.prev_end = curr_tok.location.end;
        }

        if let Some(next) = self.token_stream.next() {
            self.current_start = next.location.start;
            self.curr_tok = Some(next);
            true
        } else {
            false
        }
    }

    fn next(&mut self) -> Result<(), ParserError> {
        if let Some(ref curr_tok) = self.curr_tok {
            self.prev_end = curr_tok.location.end;
        }

        if let Some(next) = self.token_stream.next() {
            self.current_start = next.location.start;
            self.curr_tok = Some(next);
            Ok(())
        } else {
            Err(ParserError::PrematureEof)
        }
    }
}

#[derive(Debug)]
pub enum ParserError {
    PrematureEof,
}

#[cfg(test)]
mod tests {

    use crate::{
        lexer::Lexer,
        parser::{
            ast::{ExpressionNode, Operator},
            Node, Parser,
        },
        Location, Log,
    };

    use super::ast::{DesignatorNode, ProgramNode};

    #[test]
    fn test_empty_source() {
        let program_node = parse(String::new()).node_type;
        assert!(program_node.classes.is_empty());
    }

    #[test]
    fn test_two_empty_classes() {
        let program_node = parse(String::from("class A { } class B {}"));
        assert_eq!(program_node.location, Location { start: 0, end: 21 });
        let program_node = program_node.node_type;
        assert_eq!(program_node.classes.len(), 2);

        let first_class = &program_node.classes[0];
        assert_eq!(first_class.location, Location { start: 0, end: 10 });
        let first_class = &first_class.node_type;
        assert_eq!(first_class.identifier, String::from("A"));
        assert!(first_class.base_class.is_none());
        assert!(first_class.fields.is_empty());
        assert!(first_class.methods.is_empty());

        let second_class = &program_node.classes[0];
        assert_eq!(second_class.location, Location { start: 0, end: 10 });
        let second_class = &second_class.node_type;
        assert_eq!(second_class.identifier, String::from("A"));
        assert!(second_class.base_class.is_none());
        assert!(second_class.fields.is_empty());
        assert!(second_class.methods.is_empty());
    }

    #[test]
    fn test_two_fields() {
        let program_node = parse(String::from("class A { int[] a; boolean b; }"));
        assert_eq!(program_node.location, Location { start: 0, end: 30 });
        let program_node = program_node.node_type;
        assert_eq!(program_node.classes.len(), 1);

        let class_node = &program_node.classes[0];
        assert_eq!(class_node.location, Location { start: 0, end: 30 });
        let class_node = &class_node.node_type;
        assert_eq!(class_node.fields.len(), 2);

        let first_field = &class_node.fields[0];
        assert_eq!(first_field.location, Location { start: 10, end: 16 });
        let first_field = &first_field.node_type;
        assert_eq!(first_field.identifier, String::from("a"));
        let first_type = &first_field.var_type;
        assert_eq!(first_type.location, Location { start: 10, end: 14 });
        let first_type = &first_type.node_type;
        assert!(first_type.unwrap_array_type_node().is_some());
        assert!(first_type
            .unwrap_array_type_node()
            .unwrap()
            .element_type
            .node_type
            .unwrap_basic_type_node()
            .is_some());
        assert_eq!(
            first_type
                .unwrap_array_type_node()
                .unwrap()
                .element_type
                .node_type
                .unwrap_basic_type_node()
                .unwrap()
                .identifier,
            String::from("int")
        );

        let second_field = &class_node.fields[1];
        assert_eq!(second_field.location, Location { start: 19, end: 27 });
        let second_field = &second_field.node_type;
        assert_eq!(second_field.identifier, String::from("b"));
        let second_type = &second_field.var_type;
        assert_eq!(second_type.location, Location { start: 19, end: 25 });
        let second_type = &second_type.node_type;
        assert!(second_type.unwrap_basic_type_node().is_some());
        assert_eq!(
            second_type.unwrap_basic_type_node().unwrap().identifier,
            String::from("boolean")
        );
    }

    #[test]
    fn test_two_methods() {
        let program_node = parse(String::from(
            "class A { void main() { ;; } int do(A x, string y) {} }",
        ));
        assert_eq!(program_node.location, Location { start: 0, end: 54 });
        let program_node = program_node.node_type;
        assert_eq!(program_node.classes.len(), 1);

        let class_node = &program_node.classes[0];
        assert_eq!(class_node.location, Location { start: 0, end: 54 });
        let class_node = &class_node.node_type;
        assert_eq!(class_node.methods.len(), 2);

        let main_method = &class_node.methods[0];
        assert_eq!(main_method.location, Location { start: 10, end: 27 });
        let main_method = &main_method.node_type;
        assert_eq!(main_method.identifier, String::from("main"));
        assert!(main_method.parameters.is_empty());
        let main_method_return_type = &main_method.return_type;
        assert_eq!(
            main_method_return_type.location,
            Location { start: 10, end: 13 }
        );
        let main_method_return_type = &main_method_return_type.node_type;
        assert!(main_method_return_type.unwrap_basic_type_node().is_some());
        assert_eq!(
            main_method_return_type
                .unwrap_basic_type_node()
                .unwrap()
                .identifier,
            String::from("void")
        );

        let do_method = &class_node.methods[1];
        assert_eq!(do_method.location, Location { start: 29, end: 52 });
        let do_method = &do_method.node_type;
        assert_eq!(do_method.identifier, String::from("do"));
        assert_eq!(do_method.parameters.len(), 2);

        let first_param = &do_method.parameters[0];
        assert_eq!(first_param.location, Location { start: 36, end: 38 });
        assert_eq!(first_param.node_type.identifier, String::from("x"));
        let first_param_type = &first_param.node_type.var_type;
        assert_eq!(first_param_type.location, Location { start: 36, end: 36 });
        assert!(first_param_type
            .node_type
            .unwrap_basic_type_node()
            .is_some());
        assert_eq!(
            first_param_type
                .node_type
                .unwrap_basic_type_node()
                .unwrap()
                .identifier,
            String::from("A")
        );

        let second_param = &do_method.parameters[1];
        assert_eq!(second_param.location, Location { start: 41, end: 48 });
        assert_eq!(second_param.node_type.identifier, String::from("y"));
        let second_param_type = &second_param.node_type.var_type;
        assert_eq!(second_param_type.location, Location { start: 41, end: 46 });
        assert!(second_param_type
            .node_type
            .unwrap_basic_type_node()
            .is_some());
        assert_eq!(
            second_param_type
                .node_type
                .unwrap_basic_type_node()
                .unwrap()
                .identifier,
            String::from("string")
        );

        let do_method_return_type = &do_method.return_type;
        assert_eq!(
            do_method_return_type.location,
            Location { start: 29, end: 31 }
        );
        let do_method_return_type = &do_method_return_type.node_type;
        assert!(do_method_return_type.unwrap_basic_type_node().is_some());
        assert_eq!(
            do_method_return_type
                .unwrap_basic_type_node()
                .unwrap()
                .identifier,
            String::from("int")
        );
    }

    #[test]
    fn test_local_assignments() {
        let program_node = parse(String::from(
            "class A { void main() { int[] a; string s; a = new int[100]; s = \"Hello\"; } }",
        ));
        assert_eq!(program_node.location, Location { start: 0, end: 76 });
        let program_node = program_node.node_type;
        assert_eq!(program_node.classes.len(), 1);

        let methods = &program_node.classes[0].node_type.methods;
        assert_eq!(methods.len(), 1);
        let statements = &methods[0].node_type.body;
        assert_eq!(statements.location, Location { start: 22, end: 74 });
        let statements = &statements.node_type.statements;
        assert_eq!(statements.len(), 4);

        assert_eq!(statements[0].location, Location { start: 24, end: 30 });
        assert!(statements[0]
            .node_type
            .unwrap_local_declaration_node()
            .is_some());
        let first_local = statements[0]
            .node_type
            .unwrap_local_declaration_node()
            .unwrap();
        assert_eq!(
            first_local.variable.location,
            Location { start: 24, end: 30 }
        );
        assert_eq!(first_local.variable.node_type.identifier, String::from("a"));
        let first_local_type = &first_local.variable.node_type.var_type;
        assert_eq!(first_local_type.location, Location { start: 24, end: 28 });
        assert!(first_local_type
            .node_type
            .unwrap_array_type_node()
            .is_some());
        let first_local_type = first_local_type.node_type.unwrap_array_type_node().unwrap();
        assert!(first_local_type
            .element_type
            .node_type
            .unwrap_basic_type_node()
            .is_some());
        assert_eq!(
            first_local_type
                .element_type
                .node_type
                .unwrap_basic_type_node()
                .unwrap()
                .identifier,
            String::from("int")
        );

        assert_eq!(statements[1].location, Location { start: 33, end: 40 });
        assert!(statements[1]
            .node_type
            .unwrap_local_declaration_node()
            .is_some());
        let second_local = statements[1]
            .node_type
            .unwrap_local_declaration_node()
            .unwrap();
        assert_eq!(
            second_local.variable.location,
            Location { start: 33, end: 40 }
        );
        assert_eq!(
            second_local.variable.node_type.identifier,
            String::from("s")
        );
        let second_local_type = &second_local.variable.node_type.var_type;
        assert_eq!(second_local_type.location, Location { start: 33, end: 38 });
        assert!(second_local_type
            .node_type
            .unwrap_basic_type_node()
            .is_some());
        let second_local_type = second_local_type
            .node_type
            .unwrap_basic_type_node()
            .unwrap();
        assert_eq!(second_local_type.identifier, String::from("string"));

        assert_eq!(statements[2].location, Location { start: 43, end: 58 });
        assert!(statements[2].node_type.unwrap_assignment_node().is_some());
        let first_assignment = statements[2].node_type.unwrap_assignment_node().unwrap();
        assert_basic_designator(&first_assignment.left, String::from("a"), 43, 43);
        assert_eq!(
            first_assignment.right.location,
            Location { start: 47, end: 58 }
        );
        assert!(first_assignment
            .right
            .node_type
            .unwrap_array_creation_node()
            .is_some());
        let array_creation_node = first_assignment
            .right
            .node_type
            .unwrap_array_creation_node()
            .unwrap();
        assert_eq!(
            array_creation_node.element_type.location,
            Location { start: 51, end: 53 }
        );
        assert!(array_creation_node
            .element_type
            .node_type
            .unwrap_basic_type_node()
            .is_some());
        let array_element_type = array_creation_node
            .element_type
            .node_type
            .unwrap_basic_type_node()
            .unwrap();
        assert_eq!(array_element_type.identifier, String::from("int"));
        assert_eq!(
            array_creation_node.expression.location,
            Location { start: 55, end: 57 }
        );
        assert!(array_creation_node
            .expression
            .node_type
            .unwrap_integer_literal_node()
            .is_some());
        let array_expression = array_creation_node
            .expression
            .node_type
            .unwrap_integer_literal_node()
            .unwrap();
        assert_eq!(array_expression.val, 100);

        assert_eq!(statements[3].location, Location { start: 61, end: 71 });
        assert!(statements[3].node_type.unwrap_assignment_node().is_some());
        let second_assignment = statements[3].node_type.unwrap_assignment_node().unwrap();
        assert_basic_designator(&second_assignment.left, String::from("s"), 61, 61);
        assert_string_literal(&second_assignment.right, String::from("Hello"), 65, 71);
    }

    #[test]
    fn test_complex_expression() {
        let program_node = parse(String::from(
            "class A { void main() { x = 1 + 2 * 3 <= 4 - 5 - 6 && !b || (c == -d); } }",
        ));
        assert_eq!(program_node.location, Location { start: 0, end: 73 });
        let program_node = program_node.node_type;
        assert_eq!(program_node.classes.len(), 1);
        assert_eq!(program_node.classes[0].node_type.methods.len(), 1);
        let method = &program_node.classes[0].node_type.methods[0];
        assert_eq!(method.node_type.body.node_type.statements.len(), 1);
        let statement = &method.node_type.body.node_type.statements[0];
        assert_eq!(statement.location, Location { start: 24, end: 68 });
        assert!(statement.node_type.unwrap_assignment_node().is_some());

        let assignment_node = statement.node_type.unwrap_assignment_node().unwrap();
        assert_eq!(
            assignment_node.right.location,
            Location { start: 28, end: 68 }
        );
        assert!(assignment_node
            .right
            .node_type
            .unwrap_binary_expression_node()
            .is_some());
        let or_expression = assignment_node
            .right
            .node_type
            .unwrap_binary_expression_node()
            .unwrap();
        assert_eq!(or_expression.op, Operator::Or);

        assert_eq!(or_expression.left.location, Location { start: 28, end: 55 });
        assert!(or_expression
            .left
            .node_type
            .unwrap_binary_expression_node()
            .is_some());
        let and_expression = or_expression
            .left
            .node_type
            .unwrap_binary_expression_node()
            .unwrap();
        assert_eq!(and_expression.op, Operator::And);

        assert_eq!(
            and_expression.left.location,
            Location { start: 28, end: 49 }
        );
        assert!(and_expression
            .left
            .node_type
            .unwrap_binary_expression_node()
            .is_some());
        let less_equal_expression = and_expression
            .left
            .node_type
            .unwrap_binary_expression_node()
            .unwrap();
        assert_eq!(less_equal_expression.op, Operator::LessEqual);

        assert_eq!(
            less_equal_expression.left.location,
            Location { start: 28, end: 36 }
        );
        assert!(less_equal_expression
            .left
            .node_type
            .unwrap_binary_expression_node()
            .is_some());
        let one_two_three = less_equal_expression
            .left
            .node_type
            .unwrap_binary_expression_node()
            .unwrap();
        assert_eq!(one_two_three.op, Operator::Plus);
        assert_int_literal(&one_two_three.left, 1, 28, 28);

        assert_eq!(
            one_two_three.right.location,
            Location { start: 32, end: 36 }
        );
        assert!(one_two_three
            .right
            .node_type
            .unwrap_binary_expression_node()
            .is_some());
        let two_three = one_two_three
            .right
            .node_type
            .unwrap_binary_expression_node()
            .unwrap();
        assert_eq!(two_three.op, Operator::Times);
        assert_int_literal(&two_three.left, 2, 32, 32);
        assert_int_literal(&two_three.right, 3, 36, 36);

        assert_eq!(
            less_equal_expression.right.location,
            Location { start: 41, end: 49 }
        );
        assert!(less_equal_expression
            .right
            .node_type
            .unwrap_binary_expression_node()
            .is_some());
        let four_five_six = less_equal_expression
            .right
            .node_type
            .unwrap_binary_expression_node()
            .unwrap();
        assert_eq!(four_five_six.op, Operator::Minus);
        assert_eq!(four_five_six.left.location, Location { start: 41, end: 45 });
        assert!(four_five_six
            .left
            .node_type
            .unwrap_binary_expression_node()
            .is_some());
        let four_five = four_five_six
            .left
            .node_type
            .unwrap_binary_expression_node()
            .unwrap();
        assert_eq!(four_five.op, Operator::Minus);
        assert_int_literal(&four_five.left, 4, 41, 41);
        assert_int_literal(&four_five.right, 5, 45, 45);
        assert_int_literal(&four_five_six.right, 6, 49, 49);

        assert_eq!(
            and_expression.right.location,
            Location { start: 54, end: 55 }
        );
        assert!(and_expression
            .right
            .node_type
            .unwrap_unary_expression_node()
            .is_some());
        let not_expression = and_expression
            .right
            .node_type
            .unwrap_unary_expression_node()
            .unwrap();
        assert_eq!(not_expression.op, Operator::Not);
        assert_basic_designator_expression(&not_expression.operand, String::from("b"), 55, 55);

        assert_eq!(
            or_expression.right.location,
            Location { start: 61, end: 67 }
        );
        assert!(or_expression
            .right
            .node_type
            .unwrap_binary_expression_node()
            .is_some());
        let equals_expression = or_expression
            .right
            .node_type
            .unwrap_binary_expression_node()
            .unwrap();
        assert_eq!(equals_expression.op, Operator::Equal);
        assert_basic_designator_expression(&equals_expression.left, String::from("c"), 61, 61);
        assert_eq!(
            equals_expression.right.location,
            Location { start: 66, end: 67 }
        );
        assert!(equals_expression
            .right
            .node_type
            .unwrap_unary_expression_node()
            .is_some());
        let negate_expression = equals_expression
            .right
            .node_type
            .unwrap_unary_expression_node()
            .unwrap();
        assert_eq!(negate_expression.op, Operator::Minus);
        assert_basic_designator_expression(&negate_expression.operand, String::from("d"), 67, 67);
    }

    #[test]
    fn test_nested_if_statement() {
        let program_node = parse(String::from(
            "class A { void main() { if (b) { if (c) { x = 1; y = 2; } else { z = 3; } } } }",
        ));
        assert_eq!(program_node.location, Location { start: 0, end: 78 });
        let program_node = program_node.node_type;
        assert_eq!(program_node.classes.len(), 1);
        assert_eq!(program_node.classes[0].node_type.methods.len(), 1);
        let method = &program_node.classes[0].node_type.methods[0];
        assert_eq!(method.node_type.body.node_type.statements.len(), 1);
        let statement = &method.node_type.body.node_type.statements[0];
        assert_eq!(statement.location, Location { start: 24, end: 74 });

        assert!(statement.node_type.unwrap_if_statement_node().is_some());
        let outer_if_statement = statement.node_type.unwrap_if_statement_node().unwrap();
        assert!(outer_if_statement.else_block.is_none());
        assert_basic_designator_expression(
            &outer_if_statement.condition,
            String::from("b"),
            28,
            28,
        );
        assert_eq!(
            outer_if_statement.then_block.location,
            Location { start: 31, end: 74 }
        );
        assert_eq!(outer_if_statement.then_block.node_type.statements.len(), 1);

        let inner_if_statement = &outer_if_statement.then_block.node_type.statements[0];
        assert_eq!(inner_if_statement.location, Location { start: 33, end: 72 });
        assert!(inner_if_statement
            .node_type
            .unwrap_if_statement_node()
            .is_some());
        let inner_if_statement = inner_if_statement
            .node_type
            .unwrap_if_statement_node()
            .unwrap();
        assert_basic_designator_expression(
            &inner_if_statement.condition,
            String::from("c"),
            37,
            37,
        );
        assert_eq!(
            inner_if_statement.then_block.location,
            Location { start: 40, end: 56 }
        );
        assert_eq!(inner_if_statement.then_block.node_type.statements.len(), 2);
        assert!(inner_if_statement.else_block.is_some());
        assert_eq!(
            inner_if_statement.else_block.as_ref().unwrap().location,
            Location { start: 63, end: 72 }
        );
        assert_eq!(
            inner_if_statement
                .else_block
                .as_ref()
                .unwrap()
                .node_type
                .statements
                .len(),
            1
        );
    }

    #[test]
    fn test_while_statements() {
        let program_node = parse(String::from(
            "class A { void main() { while (b) { while (c) { x = 1; y = 2; } } } }",
        ));
        assert_eq!(program_node.location, Location { start: 0, end: 68 });
        let program_node = program_node.node_type;
        assert_eq!(program_node.classes.len(), 1);
        assert_eq!(program_node.classes[0].node_type.methods.len(), 1);
        let method = &program_node.classes[0].node_type.methods[0];
        assert_eq!(method.node_type.body.node_type.statements.len(), 1);
        let statement = &method.node_type.body.node_type.statements[0];
        assert_eq!(statement.location, Location { start: 24, end: 64 });

        assert!(statement.node_type.unwrape_while_statement_node().is_some());
        let outer_while = statement.node_type.unwrape_while_statement_node().unwrap();
        assert_basic_designator_expression(&outer_while.condition, String::from("b"), 31, 31);

        assert_eq!(outer_while.body.location, Location { start: 34, end: 64 });
        assert_eq!(outer_while.body.node_type.statements.len(), 1);
        let inner_while = &outer_while.body.node_type.statements[0];
        assert_eq!(inner_while.location, Location { start: 36, end: 62 });
        assert!(inner_while
            .node_type
            .unwrape_while_statement_node()
            .is_some());
        let inner_while = inner_while
            .node_type
            .unwrape_while_statement_node()
            .unwrap();
        assert_basic_designator_expression(&inner_while.condition, String::from("c"), 43, 43);
        assert_eq!(inner_while.body.location, Location { start: 46, end: 62 });
        assert_eq!(inner_while.body.node_type.statements.len(), 2);
    }

    #[test]
    fn test_method_calls() {
        let program_node = parse(String::from(
            "class A { void main() { call(1, 2, 3); this.x = func(5 % 4); } }",
        ));
        assert_eq!(program_node.location, Location { start: 0, end: 63 });
        let program_node = program_node.node_type;
        assert_eq!(program_node.classes.len(), 1);
        assert_eq!(program_node.classes[0].node_type.methods.len(), 1);
        let method = &program_node.classes[0].node_type.methods[0];
        let statements = &method.node_type.body.node_type.statements;
        assert_eq!(statements.len(), 2);

        let first_call = &statements[0];
        assert_eq!(first_call.location, Location { start: 24, end: 36 });
        assert!(first_call.node_type.unwrap_call_statement_node().is_some());
        let first_call = &first_call
            .node_type
            .unwrap_call_statement_node()
            .unwrap()
            .call;
        assert_eq!(first_call.location, Location { start: 24, end: 36 });
        assert_basic_designator(
            &first_call.node_type.designator,
            String::from("call"),
            24,
            27,
        );

        let first_call_args = &first_call.node_type.arguments;
        assert_eq!(first_call_args.len(), 3);
        assert_int_literal(&first_call_args[0], 1, 29, 29);
        assert_int_literal(&first_call_args[1], 2, 32, 32);
        assert_int_literal(&first_call_args[2], 3, 35, 35);

        let assignment_node = &statements[1];
        assert_eq!(assignment_node.location, Location { start: 39, end: 58 });
        assert!(assignment_node.node_type.unwrap_assignment_node().is_some());
        let assignment_node = assignment_node.node_type.unwrap_assignment_node().unwrap();
        assert_eq!(
            assignment_node.left.location,
            Location { start: 39, end: 44 }
        );
        assert!(assignment_node
            .left
            .node_type
            .unwrap_member_access_node()
            .is_some());
        let member_access_node = assignment_node
            .left
            .node_type
            .unwrap_member_access_node()
            .unwrap();
        assert_eq!(member_access_node.identifier, String::from("x"));
        assert_basic_designator(&member_access_node.designator, String::from("this"), 39, 42);

        let second_call = &assignment_node.right;
        assert_eq!(second_call.location, Location { start: 48, end: 58 });
        assert!(second_call.node_type.unwrap_method_call_node().is_some());
        let second_call = second_call.node_type.unwrap_method_call_node().unwrap();
        let second_call_args = &second_call.arguments;
        assert_eq!(second_call_args.len(), 1);
        assert_eq!(
            second_call_args[0].location,
            Location { start: 53, end: 57 }
        );
        assert!(second_call_args[0]
            .node_type
            .unwrap_binary_expression_node()
            .is_some());
        let second_call_arg = second_call_args[0]
            .node_type
            .unwrap_binary_expression_node()
            .unwrap();
        assert_eq!(second_call_arg.op, Operator::Modulo);
        assert_int_literal(&second_call_arg.left, 5, 53, 53);
        assert_int_literal(&second_call_arg.right, 4, 57, 57);
    }

    #[test]
    fn test_method_returns() {
        let program_node = parse(String::from(
            "class A { void test() { return; return 2 * 3; } }",
        ));
        assert_eq!(program_node.location, Location { start: 0, end: 48 });
        let program_node = program_node.node_type;
        assert_eq!(program_node.classes.len(), 1);
        assert_eq!(program_node.classes[0].node_type.methods.len(), 1);
        let method = &program_node.classes[0].node_type.methods[0];
        let statements = &method.node_type.body.node_type.statements;
        assert_eq!(statements.len(), 2);

        assert_eq!(statements[0].location, Location { start: 24, end: 29 });
        assert!(statements[0]
            .node_type
            .unwrap_return_statement_node()
            .is_some());
        let first_return_statement = statements[0]
            .node_type
            .unwrap_return_statement_node()
            .unwrap();
        assert!(first_return_statement.expression.is_none());

        assert_eq!(statements[1].location, Location { start: 32, end: 43 });
        assert!(statements[1]
            .node_type
            .unwrap_return_statement_node()
            .is_some());
        let second_return_statement = statements[1]
            .node_type
            .unwrap_return_statement_node()
            .unwrap();
        assert!(second_return_statement.expression.is_some());
        assert_eq!(
            second_return_statement
                .expression
                .as_ref()
                .unwrap()
                .location,
            Location { start: 39, end: 43 }
        );
        assert!(second_return_statement
            .expression
            .as_ref()
            .unwrap()
            .node_type
            .unwrap_binary_expression_node()
            .is_some());
        let second_return_expression = second_return_statement
            .expression
            .as_ref()
            .unwrap()
            .node_type
            .unwrap_binary_expression_node()
            .unwrap();
        assert_eq!(second_return_expression.op, Operator::Times);
        assert_int_literal(&second_return_expression.left, 2, 39, 39);
        assert_int_literal(&second_return_expression.right, 3, 43, 43);
    }

    #[test]
    fn test_complex_designators() {
        let program_node = parse(String::from(
            "class A { void test() { a[1 + b.f].g[0].h = x.y[2].z(); } }",
        ));
        assert_eq!(program_node.location, Location { start: 0, end: 58 });
        let program_node = program_node.node_type;
        assert_eq!(program_node.classes.len(), 1);
        assert_eq!(program_node.classes[0].node_type.methods.len(), 1);
        let method = &program_node.classes[0].node_type.methods[0];
        assert_eq!(method.node_type.body.node_type.statements.len(), 1);
        let statement = &method.node_type.body.node_type.statements[0];
        assert_eq!(statement.location, Location { start: 24, end: 53 });

        assert!(statement.node_type.unwrap_assignment_node().is_some());
        let assignment_node = statement.node_type.unwrap_assignment_node().unwrap();

        assert_eq!(
            assignment_node.left.location,
            Location { start: 24, end: 40 }
        );
        assert!(assignment_node
            .left
            .node_type
            .unwrap_member_access_node()
            .is_some());

        let left1 = assignment_node
            .left
            .node_type
            .unwrap_member_access_node()
            .unwrap();
        assert_eq!(left1.identifier, String::from("h"));
        assert_eq!(left1.designator.location, Location { start: 24, end: 38 });
        assert!(left1
            .designator
            .node_type
            .unwrap_element_access_node()
            .is_some());

        let left2 = left1
            .designator
            .node_type
            .unwrap_element_access_node()
            .unwrap();
        assert_int_literal(&left2.expression, 0, 37, 37);
        assert_eq!(left2.designator.location, Location { start: 24, end: 35 });
        assert!(left2
            .designator
            .node_type
            .unwrap_member_access_node()
            .is_some());

        let left3 = left2
            .designator
            .node_type
            .unwrap_member_access_node()
            .unwrap();
        assert_eq!(left3.identifier, String::from("g"));
        assert_eq!(left3.designator.location, Location { start: 24, end: 33 });
        assert!(left3
            .designator
            .node_type
            .unwrap_element_access_node()
            .is_some());

        let left4 = left3
            .designator
            .node_type
            .unwrap_element_access_node()
            .unwrap();
        assert_basic_designator(&left4.designator, String::from("a"), 24, 24);
        assert_eq!(left4.expression.location, Location { start: 26, end: 32 });
        assert!(left4
            .expression
            .node_type
            .unwrap_binary_expression_node()
            .is_some());
        let left4_expression = left4
            .expression
            .node_type
            .unwrap_binary_expression_node()
            .unwrap();
        assert_int_literal(&left4_expression.left, 1, 26, 26);
        assert_eq!(
            left4_expression.right.location,
            Location { start: 30, end: 32 }
        );
        assert!(left4_expression
            .right
            .node_type
            .unwrap_member_access_node()
            .is_some());
        let left4_expression_inner = left4_expression
            .right
            .node_type
            .unwrap_member_access_node()
            .unwrap();
        assert_eq!(left4_expression_inner.identifier, String::from("f"));
        assert_basic_designator(
            &left4_expression_inner.designator,
            String::from("b"),
            30,
            30,
        );

        assert_eq!(
            assignment_node.right.location,
            Location { start: 44, end: 53 }
        );
        assert!(assignment_node
            .right
            .node_type
            .unwrap_method_call_node()
            .is_some());
        let call_node = assignment_node
            .right
            .node_type
            .unwrap_method_call_node()
            .unwrap();
        assert_eq!(call_node.arguments.len(), 0);
        assert_eq!(
            call_node.designator.location,
            Location { start: 44, end: 51 }
        );
        assert!(call_node
            .designator
            .node_type
            .unwrap_member_access_node()
            .is_some());

        let right1 = call_node
            .designator
            .node_type
            .unwrap_member_access_node()
            .unwrap();
        assert_eq!(right1.identifier, String::from("z"));
        assert_eq!(right1.designator.location, Location { start: 44, end: 49 });
        assert!(right1
            .designator
            .node_type
            .unwrap_element_access_node()
            .is_some());

        let right2 = right1
            .designator
            .node_type
            .unwrap_element_access_node()
            .unwrap();
        assert_int_literal(&right2.expression, 2, 48, 48);
        assert_eq!(right2.designator.location, Location { start: 44, end: 46 });
        assert!(right2
            .designator
            .node_type
            .unwrap_member_access_node()
            .is_some());

        let right3 = right2
            .designator
            .node_type
            .unwrap_member_access_node()
            .unwrap();
        assert_eq!(right3.identifier, String::from("y"));
        assert_basic_designator(&right3.designator, String::from("x"), 44, 44);
    }

    #[inline]
    fn assert_basic_designator(
        node: &Box<Node<dyn DesignatorNode>>,
        val: String,
        start: usize,
        end: usize,
    ) {
        assert_eq!(node.location, Location { start, end });
        assert!(node.node_type.unwrap_basic_designator_node().is_some());
        assert_eq!(
            node.node_type
                .unwrap_basic_designator_node()
                .unwrap()
                .identifier,
            val
        );
    }

    #[inline]
    fn assert_basic_designator_expression(
        node: &Box<Node<dyn ExpressionNode>>,
        val: String,
        start: usize,
        end: usize,
    ) {
        assert_eq!(node.location, Location { start, end });
        assert!(node.node_type.unwrap_basic_designator_node().is_some());
        assert_eq!(
            node.node_type
                .unwrap_basic_designator_node()
                .unwrap()
                .identifier,
            val
        );
    }

    #[inline]
    fn assert_string_literal(
        node: &Box<Node<dyn ExpressionNode>>,
        val: String,
        start: usize,
        end: usize,
    ) {
        assert_eq!(node.location, Location { start, end });
        assert!(node.node_type.unwrap_string_literal_node().is_some());
        assert_eq!(
            node.node_type.unwrap_string_literal_node().unwrap().val,
            val
        );
    }

    #[inline]
    fn assert_int_literal(
        node: &Box<Node<dyn ExpressionNode>>,
        val: i32,
        start: usize,
        end: usize,
    ) {
        assert_eq!(node.location, Location { start, end });
        assert!(node.node_type.unwrap_integer_literal_node().is_some());
        assert_eq!(
            node.node_type.unwrap_integer_literal_node().unwrap().val,
            val
        );
    }

    fn parse(source: String) -> Node<ProgramNode> {
        let mut log = Log { errors: Vec::new() };
        let lexer = Lexer::new_for_string(source, &mut log);
        let token_stream = lexer.read_token_stream();
        assert!(log.errors.is_empty());
        let parser = Parser::new(token_stream, &mut log);
        let program_node = parser.parse_program();
        assert!(program_node.is_ok());
        assert!(log.errors.is_empty());
        program_node.unwrap()
    }
}
