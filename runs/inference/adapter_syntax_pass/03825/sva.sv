module binary_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       CTRL,
    input logic [3:0] C
);

    // When CTRL is low, C is the 4-bit sum of A and B.
    check_ctrl_low_sum: assert property (
        @($global_clock) (CTRL == 1'b0) |-> (C == (A + B))
    );

    // When CTRL is high, C is the 4-bit sum of the upper three bits of A and B.
    check_ctrl_high_sum: assert property (
        @($global_clock) (CTRL == 1'b1) |-> (C == ({1'b0, A[3:1]} + {1'b0, B[3:1]}))
    );

    // In CTRL-high mode, the least-significant bit of C is always zero.
    check_ctrl_high_lsb_zero: assert property (
        @($global_clock) (CTRL == 1'b1) |-> (C[0] == 1'b0)
    );

    // In CTRL-high mode, the upper three bits of C are the sum of A[3:1] and B[3:1].
    check_ctrl_high_upper_bits_sum: assert property (
        @($global_clock) (CTRL == 1'b1) |-> (C[3:1] == (A[3:1] + B[3:1]))
    );

endmodule