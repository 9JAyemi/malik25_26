module calculator_sva (
    input logic CLK,
    input logic [7:0] num1,
    input logic [7:0] num2,
    input logic control,
    input logic [7:0] result,
    input logic carry
);

    ///// Core functionality /////
    // When control==0, outputs equal 9-bit unsigned addition.
    check_add_operation: assert property (
        @(posedge CLK) (control == 1'b0) |-> ({carry, result} == ({1'b0, num1} + {1'b0, num2}))
    );

    // When control==1, outputs equal 9-bit unsigned subtraction.
    check_sub_operation: assert property (
        @(posedge CLK) (control == 1'b1) |-> ({carry, result} == ({1'b0, num1} - {1'b0, num2}))
    );

    ///// Carry/borrow semantics /////
    // In addition mode, carry equals MSB of 9-bit sum.
    check_add_carry_bit: assert property (
        @(posedge CLK) (control == 1'b0) |-> (carry == (({1'b0, num1} + {1'b0, num2})[8]))
    );

    // In subtraction mode, carry indicates borrow (num1 < num2).
    check_sub_borrow_flag: assert property (
        @(posedge CLK) (control == 1'b1) |-> (carry == (num1 < num2))
    );

    ///// Simple algebraic corollaries /////
    // Addition by zero passes through num2 with no carry.
    check_add_zero_num1: assert property (
        @(posedge CLK) (control == 1'b0 && (num1 == 8'h00)) |-> (result == num2 && carry == 1'b0)
    );

    // Addition by zero passes through num1 with no carry.
    check_add_zero_num2: assert property (
        @(posedge CLK) (control == 1'b0 && (num2 == 8'h00)) |-> (result == num1 && carry == 1'b0)
    );

    // Subtraction by zero passes through num1 with no borrow.
    check_sub_zero_num2: assert property (
        @(posedge CLK) (control == 1'b1 && (num2 == 8'h00)) |-> (result == num1 && carry == 1'b0)
    );

    // Subtraction of equal operands yields zero with no borrow.
    check_sub_equal_operands: assert property (
        @(posedge CLK) (control == 1'b1 && (num1 == num2)) |-> (result == 8'h00 && carry == 1'b0)
    );

    ///// Edge-case spot checks /////
    // 0xFF + 0x01 => 0x00 with carry 1 in addition mode.
    check_add_overflow_case: assert property (
        @(posedge CLK) (control == 1'b0 && num1 == 8'hFF && num2 == 8'h01) |-> (result == 8'h00 && carry == 1'b1)
    );

    // 0x00 - 0x01 => 0xFF with borrow (carry=1) in subtraction mode.
    check_sub_borrow_case: assert property (
        @(posedge CLK) (control == 1'b1 && num1 == 8'h00 && num2 == 8'h01) |-> (result == 8'hFF && carry == 1'b1)
    );

endmodule