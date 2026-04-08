module AdderSubtractor_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Sub,
    input logic [3:0] S,
    input logic Cout
);

    // Addition mode returns the 4-bit sum.
    check_add_sum: assert property (
        @(posedge clk) (Sub == 1'b0) |-> (S == (A + B))
    );

    // Addition mode never asserts Cout.
    check_add_cout_low: assert property (
        @(posedge clk) (Sub == 1'b0) |-> (Cout == 1'b0)
    );

    // Subtraction mode returns the 4-bit difference.
    check_sub_diff: assert property (
        @(posedge clk) (Sub == 1'b1) |-> (S == (A - B))
    );

    // Subtraction mode uses A>=B as the Cout flag.
    check_sub_cout_no_borrow: assert property (
        @(posedge clk) (Sub == 1'b1) |-> (Cout == (A >= B))
    );

    // Equal operands subtract to zero with Cout asserted.
    check_sub_equal_zero: assert property (
        @(posedge clk) (Sub == 1'b1 && A == B) |-> (S == 4'b0000 && Cout == 1'b1)
    );

    // Adding zero passes A through and keeps Cout low.
    check_add_zero_passthrough: assert property (
        @(posedge clk) (Sub == 1'b0 && B == 4'b0000) |-> (S == A && Cout == 1'b0)
    );

    // Subtracting zero passes A through and asserts Cout.
    check_sub_zero_passthrough: assert property (
        @(posedge clk) (Sub == 1'b1 && B == 4'b0000) |-> (S == A && Cout == 1'b1)
    );

    // 0xF + 0x1 wraps to zero and still leaves Cout low.
    check_add_overflow_wrap: assert property (
        @(posedge clk) (Sub == 1'b0 && A == 4'hF && B == 4'h1) |-> (S == 4'h0 && Cout == 1'b0)
    );

    // 0x0 - 0x1 wraps to 0xF with Cout deasserted.
    check_sub_underflow_wrap: assert property (
        @(posedge clk) (Sub == 1'b1 && A == 4'h0 && B == 4'h1) |-> (S == 4'hF && Cout == 1'b0)
    );

endmodule