use std::{fmt::Debug, mem};

use crate::{lexer::Tag, Location};

use super::visitor::Visitor;

#[derive(Clone, Debug, PartialEq)]
pub enum Operator {
    And,
    Divide,
    Equal,
    Greater,
    GreaterEqual,
    InstanceOf,
    Less,
    LessEqual,
    Modulo,
    Minus,
    Not,
    Or,
    Plus,
    Times,
    Unequal,
}

impl Operator {
    pub fn for_unary_operator_tag(tag: &Tag) -> Option<Self> {
        match *tag {
            Tag::Not => Some(Operator::Not),
            Tag::Plus => Some(Operator::Plus),
            Tag::Minus => Some(Operator::Minus),
            _ => None,
        }
    }

    pub fn for_math_term_operator_tag(tag: &Tag) -> Option<Self> {
        match *tag {
            Tag::Times => Some(Operator::Times),
            Tag::Divide => Some(Operator::Divide),
            Tag::Modulo => Some(Operator::Modulo),
            _ => None,
        }
    }

    pub fn for_simple_math_operator_tag(tag: &Tag) -> Option<Self> {
        match *tag {
            Tag::Plus => Some(Operator::Plus),
            Tag::Minus => Some(Operator::Minus),
            _ => None,
        }
    }

    pub fn for_compare_operator_tag(tag: &Tag) -> Option<Self> {
        match *tag {
            Tag::Equal => Some(Operator::Equal),
            Tag::Unequal => Some(Operator::Unequal),
            Tag::Less => Some(Operator::Less),
            Tag::LessEqual => Some(Operator::LessEqual),
            Tag::Greater => Some(Operator::Greater),
            Tag::GreaterEqual => Some(Operator::GreaterEqual),
            Tag::InstanceOf => Some(Operator::InstanceOf),
            _ => None,
        }
    }
}

pub trait NodeType: Debug {
    fn accept(&self, visitor: &dyn Visitor);
}

pub trait ExpressionNode: NodeType {
    fn unwrap_array_creation_node(&self) -> Option<&ArrayCreationNode> {
        None
    }

    fn unwrap_basic_designator_node(&self) -> Option<&BasicDesignatorNode> {
        None
    }

    fn unwrap_binary_expression_node(&self) -> Option<&BinaryExpressionNode> {
        None
    }

    fn unwrap_element_access_node(&self) -> Option<&ElementAccessNode> {
        None
    }

    fn unwrap_integer_literal_node(&self) -> Option<&IntegerLiteralNode> {
        None
    }

    fn unwrap_member_access_node(&self) -> Option<&MemberAccessNode> {
        None
    }

    fn unwrap_method_call_node(&self) -> Option<&MethodCallNode> {
        None
    }

    fn unwrap_string_literal_node(&self) -> Option<&StringLiteralNode> {
        None
    }

    fn unwrap_unary_expression_node(&self) -> Option<&UnaryExpressionNode> {
        None
    }
}

pub trait DesignatorNode: ExpressionNode {
    /// Move contents into a Box<Node<dyn ExpressionNode>> leaving this Box<Node<dyn DesignatorNode>> unusable as a workaround until
    /// upcasting coercion is stabilised https://github.com/rust-lang/rust/issues/65991
    fn move_into_expression_node(&mut self, location: Location) -> Box<Node<dyn ExpressionNode>>;
}

pub trait TypeNode: NodeType {
    fn unwrap_array_type_node(&self) -> Option<&ArrayTypeNode> {
        None
    }

    fn unwrap_basic_type_node(&self) -> Option<&BasicTypeNode> {
        None
    }
}

pub trait StatementNode: NodeType {
    fn unwrap_assignment_node(&self) -> Option<&AssignmentNode> {
        None
    }

    fn unwrap_call_statement_node(&self) -> Option<&CallStatementNode> {
        None
    }

    fn unwrap_if_statement_node(&self) -> Option<&IfStatementNode> {
        None
    }

    fn unwrap_local_declaration_node(&self) -> Option<&LocalDeclarationNode> {
        None
    }

    fn unwrap_return_statement_node(&self) -> Option<&ReturnStatementNode> {
        None
    }

    fn unwrape_while_statement_node(&self) -> Option<&WhileStatementNode> {
        None
    }
}

#[derive(Debug)]
pub struct ArrayCreationNode {
    pub element_type: Box<Node<dyn TypeNode>>,
    pub expression: Box<Node<dyn ExpressionNode>>,
}

impl NodeType for ArrayCreationNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_array_creation_node(self);
    }
}

impl ExpressionNode for ArrayCreationNode {
    fn unwrap_array_creation_node(&self) -> Option<&ArrayCreationNode> {
        Some(self)
    }
}

#[derive(Debug)]
pub struct ArrayTypeNode {
    pub element_type: Box<Node<dyn TypeNode>>,
}

impl NodeType for ArrayTypeNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_array_type_node(self);
    }
}

impl TypeNode for ArrayTypeNode {
    fn unwrap_array_type_node(&self) -> Option<&ArrayTypeNode> {
        Some(self)
    }
}

#[derive(Debug)]
pub struct AssignmentNode {
    pub left: Box<Node<dyn DesignatorNode>>,
    pub right: Box<Node<dyn ExpressionNode>>,
}

impl NodeType for AssignmentNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_assignment_node(self);
    }
}

impl StatementNode for AssignmentNode {
    fn unwrap_assignment_node(&self) -> Option<&AssignmentNode> {
        Some(self)
    }
}

#[derive(Debug)]
pub struct BasicDesignatorNode {
    pub identifier: String,
}

impl NodeType for BasicDesignatorNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_basic_designator_node(self);
    }
}

impl ExpressionNode for BasicDesignatorNode {
    fn unwrap_basic_designator_node(&self) -> Option<&BasicDesignatorNode> {
        Some(self)
    }
}

impl DesignatorNode for BasicDesignatorNode {
    fn move_into_expression_node(&mut self, location: Location) -> Box<Node<dyn ExpressionNode>> {
        Box::new(Node {
            location,
            node_type: BasicDesignatorNode {
                identifier: mem::take(&mut self.identifier),
            },
        })
    }
}

#[derive(Debug)]
pub struct BasicTypeNode {
    pub identifier: String,
}

impl NodeType for BasicTypeNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_basic_type_node(self);
    }
}

impl TypeNode for BasicTypeNode {
    fn unwrap_basic_type_node(&self) -> Option<&BasicTypeNode> {
        Some(self)
    }
}

#[derive(Debug)]
pub struct BinaryExpressionNode {
    pub left: Box<Node<dyn ExpressionNode>>,
    pub op: Operator,
    pub right: Box<Node<dyn ExpressionNode>>,
}

impl NodeType for BinaryExpressionNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_binary_expression_node(self);
    }
}

impl ExpressionNode for BinaryExpressionNode {
    fn unwrap_binary_expression_node(&self) -> Option<&BinaryExpressionNode> {
        Some(self)
    }
}

#[derive(Debug)]
pub struct CallStatementNode {
    pub call: Node<MethodCallNode>,
}

impl NodeType for CallStatementNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_call_statement_node(self);
    }
}

impl StatementNode for CallStatementNode {
    fn unwrap_call_statement_node(&self) -> Option<&CallStatementNode> {
        Some(self)
    }
}

#[derive(Debug)]
pub struct ClassNode {
    pub identifier: String,
    pub base_class: Option<Node<BasicTypeNode>>,
    pub fields: Vec<Node<VariableNode>>,
    pub methods: Vec<Node<MethodNode>>,
}

impl NodeType for ClassNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_class_node(self);
    }
}

#[derive(Debug)]
pub struct ElementAccessNode {
    pub designator: Box<Node<dyn DesignatorNode>>,
    pub expression: Box<Node<dyn ExpressionNode>>,
}

impl NodeType for ElementAccessNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_element_access_node(self);
    }
}

impl ExpressionNode for ElementAccessNode {
    fn unwrap_element_access_node(&self) -> Option<&ElementAccessNode> {
        Some(self)
    }
}

impl DesignatorNode for ElementAccessNode {
    fn move_into_expression_node(&mut self, location: Location) -> Box<Node<dyn ExpressionNode>> {
        let dummy_designator: Box<Node<dyn DesignatorNode>> = Box::new(Node {
            location: Location::default(),
            node_type: BasicDesignatorNode {
                identifier: String::new(),
            },
        });
        let dummy_expression: Box<Node<dyn ExpressionNode>> = Box::new(Node {
            location: Location::default(),
            node_type: IntegerLiteralNode { val: 0 },
        });
        Box::new(Node {
            location,
            node_type: ElementAccessNode {
                designator: mem::replace(&mut self.designator, dummy_designator),
                expression: mem::replace(&mut self.expression, dummy_expression),
            },
        })
    }
}

#[derive(Debug)]
pub struct IfStatementNode {
    pub condition: Box<Node<dyn ExpressionNode>>,
    pub then_block: Node<StatementBlockNode>,
    pub else_block: Option<Node<StatementBlockNode>>,
}

impl NodeType for IfStatementNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_if_statement_node(self);
    }
}

impl StatementNode for IfStatementNode {
    fn unwrap_if_statement_node(&self) -> Option<&IfStatementNode> {
        Some(self)
    }
}

#[derive(Debug)]
pub struct IntegerLiteralNode {
    pub val: i32,
}

impl NodeType for IntegerLiteralNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_integer_literal_node(self);
    }
}

impl ExpressionNode for IntegerLiteralNode {
    fn unwrap_integer_literal_node(&self) -> Option<&IntegerLiteralNode> {
        Some(self)
    }
}

#[derive(Debug)]
pub struct LocalDeclarationNode {
    pub variable: Node<VariableNode>,
}

impl NodeType for LocalDeclarationNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_local_declaration_node(self);
    }
}

impl StatementNode for LocalDeclarationNode {
    fn unwrap_local_declaration_node(&self) -> Option<&LocalDeclarationNode> {
        Some(self)
    }
}

#[derive(Debug)]
pub struct MemberAccessNode {
    pub designator: Box<Node<dyn DesignatorNode>>,
    pub identifier: String,
}

impl NodeType for MemberAccessNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_member_access_node(self);
    }
}

impl ExpressionNode for MemberAccessNode {
    fn unwrap_member_access_node(&self) -> Option<&MemberAccessNode> {
        Some(self)
    }
}

impl DesignatorNode for MemberAccessNode {
    fn move_into_expression_node(&mut self, location: Location) -> Box<Node<dyn ExpressionNode>> {
        let dummy_designator: Box<Node<dyn DesignatorNode>> = Box::new(Node {
            location: Location::default(),
            node_type: BasicDesignatorNode {
                identifier: String::new(),
            },
        });
        Box::new(Node {
            location,
            node_type: MemberAccessNode {
                designator: mem::replace(&mut self.designator, dummy_designator),
                identifier: mem::take(&mut self.identifier),
            },
        })
    }
}

#[derive(Debug)]
pub struct MethodCallNode {
    pub designator: Box<Node<dyn DesignatorNode>>,
    pub arguments: Vec<Box<Node<dyn ExpressionNode>>>,
}

impl NodeType for MethodCallNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_method_call_node(self);
    }
}

impl ExpressionNode for MethodCallNode {
    fn unwrap_method_call_node(&self) -> Option<&MethodCallNode> {
        Some(self)
    }
}

#[derive(Debug)]
pub struct MethodNode {
    pub return_type: Box<Node<dyn TypeNode>>,
    pub identifier: String,
    pub parameters: Vec<Node<VariableNode>>,
    pub body: Node<StatementBlockNode>,
}

impl NodeType for MethodNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_method_node(self);
    }
}

#[derive(Debug)]
pub struct ObjectCreationNode {
    pub object_type: Node<BasicTypeNode>,
}

impl NodeType for ObjectCreationNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_object_creation_node(self);
    }
}

impl ExpressionNode for ObjectCreationNode {}

#[derive(Debug)]
pub struct ProgramNode {
    pub classes: Vec<Node<ClassNode>>,
}

impl NodeType for ProgramNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_program_node(self);
    }
}

#[derive(Debug)]
pub struct ReturnStatementNode {
    pub expression: Option<Box<Node<dyn ExpressionNode>>>,
}

impl NodeType for ReturnStatementNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_return_statement_node(self);
    }
}

impl StatementNode for ReturnStatementNode {
    fn unwrap_return_statement_node(&self) -> Option<&ReturnStatementNode> {
        Some(self)
    }
}

#[derive(Debug)]
pub struct StatementBlockNode {
    pub statements: Vec<Box<Node<dyn StatementNode>>>,
}

impl NodeType for StatementBlockNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_statement_block_node(self);
    }
}

#[derive(Debug)]
pub struct StringLiteralNode {
    pub val: String,
}

impl NodeType for StringLiteralNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_string_literal_node(self);
    }
}

impl ExpressionNode for StringLiteralNode {
    fn unwrap_string_literal_node(&self) -> Option<&StringLiteralNode> {
        Some(self)
    }
}

#[derive(Debug)]
pub struct TypeCastNode {
    pub type_node: Node<BasicTypeNode>,
    pub designator: Box<Node<dyn DesignatorNode>>,
}

impl NodeType for TypeCastNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_type_cast_node(self);
    }
}

impl ExpressionNode for TypeCastNode {}

#[derive(Debug)]
pub struct UnaryExpressionNode {
    pub op: Operator,
    pub operand: Box<Node<dyn ExpressionNode>>,
}

impl NodeType for UnaryExpressionNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_unary_expression_node(self);
    }
}

impl ExpressionNode for UnaryExpressionNode {
    fn unwrap_unary_expression_node(&self) -> Option<&UnaryExpressionNode> {
        Some(self)
    }
}

#[derive(Debug)]
pub struct VariableNode {
    pub var_type: Box<Node<dyn TypeNode>>,
    pub identifier: String,
}

impl NodeType for VariableNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_variable_node(self);
    }
}

#[derive(Debug)]
pub struct WhileStatementNode {
    pub condition: Box<Node<dyn ExpressionNode>>,
    pub body: Node<StatementBlockNode>,
}

impl NodeType for WhileStatementNode {
    fn accept(&self, visitor: &dyn Visitor) {
        visitor.visit_while_statement_node(self);
    }
}

impl StatementNode for WhileStatementNode {
    fn unwrape_while_statement_node(&self) -> Option<&WhileStatementNode> {
        Some(self)
    }
}

#[derive(Debug)]
pub struct Node<T: NodeType + ?Sized> {
    pub location: Location,
    pub node_type: T,
}

impl<T: NodeType + ?Sized> Node<T> {
    pub fn accept(&self, visitor: &dyn Visitor) {
        self.node_type.accept(visitor);
    }
}
