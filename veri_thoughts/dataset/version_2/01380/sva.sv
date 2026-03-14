module adder_subtractor_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic C,
    input logic [3:0] S,
    input logic Cout
);
    // Addition mode: S equals A + B (4-bit result).
    check_sum_add_mode: assert property (
        @(posedge clk) (!C) |-> (S == (A + B))
    );

    // Subtraction mode: S equals A + (~B + 1) (two's complement, 4-bit).
    check_sum_sub_mode: assert property (
        @(posedge clk) C |-> (S == (A + ((~B) + 4'd1)))
    );

    // Addition mode: Cout equals (A + B >= 16) as coded (with 4-bit sum semantics).
    check_cout_add_mode_expr: assert property (
        @(posedge clk) (!C) |-> (Cout == ((A + B) >= 32'd16))
    );

    // Subtraction mode: Cout indicates no borrow (A >= B).
    check_cout_sub_mode_expr: assert property (
        @(posedge clk) C |-> (Cout == (A >= B))
    );

    // Subtraction mode: when A == B, result is zero and no borrow.
    check_sub_equal_inputs_zero: assert property (
        @(posedge clk) (C && (A == B)) |-> (S == 4'd0 && Cout == 1'b1)
    );

    // Addition mode: when B == 0, pass-through A to S.
    check_add_b_zero_passthrough: assert property (
        @(posedge clk) (!C && (B == 4'd0)) |-> (S == A)
    );

    // Addition mode: when B == 0, Cout is zero per coded compare.
    check_add_b_zero_no_carry: assert property (
        @(posedge clk) (!C && (B == 4'd0)) |-> (Cout == 1'b0)
    );

    // Addition mode: when A == 0, pass-through B to S.
    check_add_a_zero_passthrough: assert property (
        @(posedge clk) (!C && (A == 4'd0)) |-> (S == B)
    );

    // Subtraction mode: when B == 0, pass-through A to S.
    check_sub_b_zero_passthrough: assert property (
        @(posedge clk) (C && (B == 4'd0)) |-> (S == A)
    );

    // Subtraction mode: when B == 0, Cout is one (A >= 0).
    check_sub_b_zero_no_borrow: assert property (
        @(posedge clk) (C && (B == 4'd0)) |-> (Cout == 1'b1)
    );
endmodule