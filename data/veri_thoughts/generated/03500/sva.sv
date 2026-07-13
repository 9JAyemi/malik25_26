module binary_adder_sva (
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C,
    input logic       Cout
);

    // C is the 8-bit sum of A and B.
    check_sum_matches_inputs: assert property (
        @($global_clock) C == (A + B)
    );

    // Cout matches the MSB of the assigned sum.
    check_cout_matches_c_msb: assert property (
        @($global_clock) Cout == C[7]
    );

    // The LSB of the sum is the XOR of the input LSBs.
    check_lsb_sum_behavior: assert property (
        @($global_clock) C[0] == (A[0] ^ B[0])
    );

    // Adding zero on B passes A through to C.
    check_b_zero_identity: assert property (
        @($global_clock) (B == 8'h00) |-> ((C == A) && (Cout == A[7]))
    );

    // Adding zero on A passes B through to C.
    check_a_zero_identity: assert property (
        @($global_clock) (A == 8'h00) |-> ((C == B) && (Cout == B[7]))
    );

endmodule