module calc_sva (
    input logic CLK,           // sampling clock for assertions
    input logic [3:0] num1,
    input logic [3:0] num2,
    input logic       op,
    input logic [3:0] result
);
    // Result matches selected operation (4-bit modular arithmetic).
    check_core_functionality: assert property (
        @(posedge CLK) result == (op ? (num1 - num2) : (num1 + num2))
    );

    // If inputs are stable across a cycle, result remains stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable(op) && $stable(num1) && $stable(num2) |-> $stable(result)
    );

    // In subtraction mode, equal operands yield zero.
    check_sub_equal_operands_zero: assert property (
        @(posedge CLK) op && (num1 == num2) |-> (result == 4'd0)
    );

    // In addition mode, adding zero on RHS yields num1.
    check_add_zero_rhs_identity: assert property (
        @(posedge CLK) (!op) && (num2 == 4'd0) |-> (result == num1)
    );

    // In addition mode, adding zero on LHS yields num2.
    check_add_zero_lhs_identity: assert property (
        @(posedge CLK) (!op) && (num1 == 4'd0) |-> (result == num2)
    );

    // In subtraction mode, subtracting zero yields num1.
    check_sub_zero_rhs_identity: assert property (
        @(posedge CLK) op && (num2 == 4'd0) |-> (result == num1)
    );

    // In subtraction mode, (result + num2) recovers num1 (mod 16).
    check_sub_invertibility_mod16: assert property (
        @(posedge CLK) op |-> ((result + num2) == num1)
    );

    // In addition mode, (result - num2) recovers num1 (mod 16).
    check_add_invertibility_mod16: assert property (
        @(posedge CLK) (!op) |-> ((result - num2) == num1)
    );
endmodule