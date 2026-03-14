module calculator_sva (
    input logic CLK,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic [7:0] result
);

    ///// Functional correctness per opcode /////
    // op=00: result equals 8-bit sum of a and b.
    check_add_result: assert property (
        @(posedge CLK) (op == 2'b00) |-> (result == ((a + b) & 8'hFF))
    );

    // op=01: result equals 8-bit difference a - b.
    check_sub_result: assert property (
        @(posedge CLK) (op == 2'b01) |-> (result == ((a - b) & 8'hFF))
    );

    // op=10: result equals low 8 bits of a * b.
    check_mul_result: assert property (
        @(posedge CLK) (op == 2'b10) |-> (result == ((a * b) & 8'hFF))
    );

    // op=11 with b!=0: result equals a / b.
    check_div_result_valid: assert property (
        @(posedge CLK) (op == 2'b11 && b != 8'd0) |-> (result == (a / b))
    );

    ///// Algebraic identities for corner cases /////
    // op=00 and b==0: result equals a.
    check_add_zero_b: assert property (
        @(posedge CLK) (op == 2'b00 && (b == 8'd0)) |-> (result == a)
    );

    // op=01 and b==0: result equals a.
    check_sub_zero_b: assert property (
        @(posedge CLK) (op == 2'b01 && (b == 8'd0)) |-> (result == a)
    );

    // op=01 and a==b: result is zero.
    check_sub_a_eq_b_zero: assert property (
        @(posedge CLK) (op == 2'b01 && (a == b)) |-> (result == 8'd0)
    );

    // op=10 and a==0 or b==0: result is zero.
    check_mul_zero_operand: assert property (
        @(posedge CLK) (op == 2'b10 && ((a == 8'd0) || (b == 8'd0))) |-> (result == 8'd0)
    );

    // op=10 and a==1: result equals b.
    check_mul_a_one: assert property (
        @(posedge CLK) (op == 2'b10 && (a == 8'd1)) |-> (result == b)
    );

    // op=10 and b==1: result equals a.
    check_mul_b_one: assert property (
        @(posedge CLK) (op == 2'b10 && (b == 8'd1)) |-> (result == a)
    );

    // op=11 and b==1: result equals a.
    check_div_b_one: assert property (
        @(posedge CLK) (op == 2'b11 && (b == 8'd1)) |-> (result == a)
    );

    // op=11 with b!=0 and a==0: result is zero.
    check_div_a_zero: assert property (
        @(posedge CLK) (op == 2'b11 && b != 8'd0 && a == 8'd0) |-> (result == 8'd0)
    );

    // op=11 with b!=0 and a==b: result is one.
    check_div_a_eq_b_one: assert property (
        @(posedge CLK) (op == 2'b11 && b != 8'd0 && a == b) |-> (result == 8'd1)
    );

endmodule