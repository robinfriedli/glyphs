use super::ast::*;

pub trait Visitor {
    fn visit_array_creation_node(&self, node: &ArrayCreationNode);

    fn visit_array_type_node(&self, node: &ArrayTypeNode);

    fn visit_assignment_node(&self, node: &AssignmentNode);

    fn visit_basic_designator_node(&self, node: &BasicDesignatorNode);

    fn visit_basic_type_node(&self, node: &BasicTypeNode);

    fn visit_binary_expression_node(&self, node: &BinaryExpressionNode);

    fn visit_call_statement_node(&self, node: &CallStatementNode);

    fn visit_class_node(&self, node: &ClassNode);

    fn visit_element_access_node(&self, node: &ElementAccessNode);

    fn visit_if_statement_node(&self, node: &IfStatementNode);

    fn visit_integer_literal_node(&self, node: &IntegerLiteralNode);

    fn visit_local_declaration_node(&self, node: &LocalDeclarationNode);

    fn visit_member_access_node(&self, node: &MemberAccessNode);

    fn visit_method_call_node(&self, node: &MethodCallNode);

    fn visit_method_node(&self, node: &MethodNode);

    fn visit_object_creation_node(&self, node: &ObjectCreationNode);

    fn visit_program_node(&self, node: &ProgramNode);

    fn visit_return_statement_node(&self, node: &ReturnStatementNode);

    fn visit_statement_block_node(&self, node: &StatementBlockNode);

    fn visit_string_literal_node(&self, node: &StringLiteralNode);

    fn visit_type_cast_node(&self, node: &TypeCastNode);

    fn visit_unary_expression_node(&self, node: &UnaryExpressionNode);

    fn visit_variable_node(&self, node: &VariableNode);

    fn visit_while_statement_node(&self, node: &WhileStatementNode);
}

pub struct BaseVisitor {}

impl Visitor for BaseVisitor {
    fn visit_array_creation_node(&self, node: &ArrayCreationNode) {
        node.element_type.accept(self);
        node.expression.accept(self);
    }

    fn visit_array_type_node(&self, node: &ArrayTypeNode) {
        node.element_type.accept(self);
    }

    fn visit_assignment_node(&self, node: &AssignmentNode) {
        node.left.accept(self);
        node.right.accept(self);
    }

    fn visit_basic_designator_node(&self, _node: &BasicDesignatorNode) {}

    fn visit_basic_type_node(&self, _node: &BasicTypeNode) {}

    fn visit_binary_expression_node(&self, node: &BinaryExpressionNode) {
        node.left.accept(self);
        node.right.accept(self);
    }

    fn visit_call_statement_node(&self, node: &CallStatementNode) {
        node.call.accept(self);
    }

    fn visit_class_node(&self, node: &ClassNode) {
        if let Some(ref base_class) = node.base_class {
            base_class.accept(self);
        }

        for field in node.fields.iter() {
            field.accept(self);
        }

        for method in node.methods.iter() {
            method.accept(self);
        }
    }

    fn visit_element_access_node(&self, node: &ElementAccessNode) {
        node.designator.accept(self);
        node.expression.accept(self);
    }

    fn visit_if_statement_node(&self, node: &IfStatementNode) {
        node.condition.accept(self);
        node.then_block.accept(self);
        if let Some(ref else_block) = node.else_block {
            else_block.accept(self);
        }
    }

    fn visit_integer_literal_node(&self, _node: &IntegerLiteralNode) {}

    fn visit_local_declaration_node(&self, node: &LocalDeclarationNode) {
        node.variable.accept(self);
    }

    fn visit_member_access_node(&self, node: &MemberAccessNode) {
        node.designator.accept(self);
    }

    fn visit_method_call_node(&self, node: &MethodCallNode) {
        node.designator.accept(self);
        for argument in node.arguments.iter() {
            argument.accept(self);
        }
    }

    fn visit_method_node(&self, node: &MethodNode) {
        node.return_type.accept(self);

        for parameter in node.parameters.iter() {
            parameter.accept(self);
        }

        node.body.accept(self);
    }

    fn visit_object_creation_node(&self, node: &ObjectCreationNode) {
        node.object_type.accept(self);
    }

    fn visit_program_node(&self, node: &ProgramNode) {
        for class_node in node.classes.iter() {
            class_node.accept(self);
        }
    }

    fn visit_return_statement_node(&self, node: &ReturnStatementNode) {
        if let Some(ref expression) = node.expression {
            expression.accept(self);
        }
    }

    fn visit_statement_block_node(&self, node: &StatementBlockNode) {
        for statement in node.statements.iter() {
            statement.accept(self);
        }
    }

    fn visit_string_literal_node(&self, _node: &StringLiteralNode) {}

    fn visit_type_cast_node(&self, node: &TypeCastNode)
    where
        Self: Sized,
    {
        node.type_node.accept(self);
        node.designator.accept(self);
    }

    fn visit_unary_expression_node(&self, node: &UnaryExpressionNode) {
        node.operand.accept(self);
    }

    fn visit_variable_node(&self, node: &VariableNode) {
        node.var_type.accept(self);
    }

    fn visit_while_statement_node(&self, node: &WhileStatementNode) {
        node.condition.accept(self);
        node.body.accept(self);
    }
}
