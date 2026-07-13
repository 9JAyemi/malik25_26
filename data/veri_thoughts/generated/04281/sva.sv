module ripple_carry_adder_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] S,
    input logic       Cout
);

    // LSB sum bit matches the first full-adder XOR equation.
    check_lsb_sum_xor: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // The lower two sum bits match 2-bit addition with carry-in.
    check_lower_two_bits_addition: assert property (
        @(posedge clk) S[1:0] == (A[1:0] + B[1:0] + Cin)
    );

    // The lower three sum bits match 3-bit addition with carry-in.
    check_lower_three_bits_addition: assert property (
        @(posedge clk) S[2:0] == (A[2:0] + B[2:0] + Cin)
    );

    // Full sum and carry match 5-bit extended addition.
    check_full_sum_with_carry: assert property (
        @(posedge clk) {Cout, S} == ({1'b0, A} + {1'b0, B} + Cin)
    );

    // Carry-out is asserted exactly when the 4-bit addition overflows.
    check_carry_out_overflow: assert property (
        @(posedge clk) Cout == (({1'b0, A} + {1'b0, B} + Cin) >= 5'd16)
    );

    // Adding zero with no carry-in passes A through unchanged.
    check_a_passthrough_when_b_zero: assert property (
        @(posedge clk) ((B == 4'b0000) && (Cin == 1'b0)) |-> ((S == A) && (Cout == 1'b0))
    );

    // Adding zero with no carry-in passes B through unchanged.
    check_b_passthrough_when_a_zero: assert property (
        @(posedge clk) ((A == 4'b0000) && (Cin == 1'b0)) |-> ((S == B) && (Cout == 1'b0))
    );

    // Stable sampled inputs imply stable sampled outputs.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({A, B, Cin}) |-> $stable({S, Cout})
    );

endmodule