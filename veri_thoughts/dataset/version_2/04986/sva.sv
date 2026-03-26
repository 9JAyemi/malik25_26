module adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] S,
    input logic       Cout
);

    // No explicit clock or reset; this RTL is purely combinational.
    // Use the formal global clock for sampling.

    // Full 5-bit result must equal A + B + Cin.
    check_full_sum_equivalence: assert property (
        @($global_clock)
        {Cout, S} == ({1'b0, A} + {1'b0, B} + {4'b0, Cin})
    );

    // Bit 0 must implement a 1-bit full-adder sum.
    check_lsb_full_adder_sum: assert property (
        @($global_clock)
        S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Bits [1:0] must match the lower 2-bit partial sum.
    check_low2_partial_sum: assert property (
        @($global_clock)
        S[1:0] == (({1'b0, A[1:0]} + {1'b0, B[1:0]} + {2'b0, Cin})[1:0])
    );

    // Bits [2:0] must match the lower 3-bit partial sum.
    check_low3_partial_sum: assert property (
        @($global_clock)
        S[2:0] == (({1'b0, A[2:0]} + {1'b0, B[2:0]} + {3'b0, Cin})[2:0])
    );

    // Cout must be the MSB of the extended 5-bit sum.
    check_carry_out_bit: assert property (
        @($global_clock)
        Cout == (({1'b0, A} + {1'b0, B} + {4'b0, Cin})[4])
    );

endmodule