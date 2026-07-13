module four_bit_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S,
    input logic Cout
);

    // S[0] matches the RTL XOR of A[0], B[0], and Cin.
    check_sum_bit0_function: assert property (
        @(posedge clk) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // S[1] matches the RTL function using S[0] and Cin.
    check_sum_bit1_function: assert property (
        @(posedge clk) S[1] == (A[1] ^ B[1] ^ (S[0] & Cin))
    );

    // S[2] matches the RTL function using S[1] and S[0].
    check_sum_bit2_function: assert property (
        @(posedge clk) S[2] == (A[2] ^ B[2] ^ (S[1] & S[0]))
    );

    // S[3] matches the RTL function using S[2] and S[1].
    check_sum_bit3_function: assert property (
        @(posedge clk) S[3] == (A[3] ^ B[3] ^ (S[2] & S[1]))
    );

    // Cout matches the RTL expression built from the sum bits and Cin.
    check_cout_function: assert property (
        @(posedge clk) Cout == ((S[3] & S[2]) | (S[3] & S[1]) | (S[2] & S[1] & Cin))
    );

    // Stable inputs must keep all outputs stable across sampled cycles.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({A, B, Cin}) |-> $stable({S, Cout})
    );

    // S[0] depends only on A[0], B[0], and Cin.
    check_sum_bit0_locality: assert property (
        @(posedge clk) $stable({A[0], B[0], Cin}) |-> $stable(S[0])
    );

    // S[1] depends only on A[1:0], B[1:0], and Cin.
    check_sum_bit1_locality: assert property (
        @(posedge clk) $stable({A[1:0], B[1:0], Cin}) |-> $stable(S[1])
    );

    // S[2] depends only on A[2:0], B[2:0], and Cin.
    check_sum_bit2_locality: assert property (
        @(posedge clk) $stable({A[2:0], B[2:0], Cin}) |-> $stable(S[2])
    );

    // Cout depends only on S[3:1] and Cin.
    check_cout_locality: assert property (
        @(posedge clk) $stable({S[3:1], Cin}) |-> $stable(Cout)
    );

endmodule