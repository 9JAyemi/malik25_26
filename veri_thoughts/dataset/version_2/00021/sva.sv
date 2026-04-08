module Adder4Bit_sva (
    input logic clk,
    input logic [3:0] S,
    input logic V,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin
);

    // S matches the implemented 4-bit addition result.
    check_sum_function: assert property (
        @(posedge clk) S == ((A + B + Cin) & 4'hF)
    );

    // V is always low in the implemented logic.
    check_v_always_low: assert property (
        @(posedge clk) V == 1'b0
    );

    // With B and Cin low, S passes A through.
    check_pass_a_when_b_and_cin_zero: assert property (
        @(posedge clk) ((B == 4'h0) && (Cin == 1'b0)) |-> (S == A)
    );

    // With A and Cin low, S passes B through.
    check_pass_b_when_a_and_cin_zero: assert property (
        @(posedge clk) ((A == 4'h0) && (Cin == 1'b0)) |-> (S == B)
    );

    // With both operands low, S reflects Cin in bit 0.
    check_zero_operands_reflect_cin: assert property (
        @(posedge clk) ((A == 4'h0) && (B == 4'h0)) |-> (S == {3'b000, Cin})
    );

    // All-zero inputs produce zero outputs.
    check_all_zero_inputs: assert property (
        @(posedge clk) ((A == 4'h0) && (B == 4'h0) && (Cin == 1'b0)) |-> ((S == 4'h0) && (V == 1'b0))
    );

endmodule