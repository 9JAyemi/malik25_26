module adder4_sva(
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);
    wire [4:0] sum;

    assign sum = A + B + Cin;

    // Combined outputs equal the computed 5-bit sum.
    check_full_sum: assert property (
        @(posedge clk) {Cout, S} == sum
    );

    // S reflects the low 4 bits of the computed sum.
    check_sum_bits: assert property (
        @(posedge clk) S == sum[3:0]
    );

    // Cout reflects the high bit of the computed sum.
    check_carry_bit: assert property (
        @(posedge clk) Cout == sum[4]
    );

    // Zero B and zero carry-in return A.
    check_identity_with_a: assert property (
        @(posedge clk) (B == 4'd0 && Cin == 1'b0) |-> ({Cout, S} == {1'b0, A})
    );

    // Zero A and zero carry-in return B.
    check_identity_with_b: assert property (
        @(posedge clk) (A == 4'd0 && Cin == 1'b0) |-> ({Cout, S} == {1'b0, B})
    );

    // Maximum inputs produce the maximum 5-bit result.
    check_maximum_input_case: assert property (
        @(posedge clk) (A == 4'hF && B == 4'hF && Cin == 1'b1) |-> ({Cout, S} == 5'h1F)
    );

    // Stable sampled inputs keep sampled outputs stable.
    check_stable_inputs_stable_outputs: assert property (
        @(posedge clk) $stable({A, B, Cin}) |-> $stable({Cout, S})
    );
endmodule