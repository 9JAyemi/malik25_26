module RippleCarryAdder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       Cin,
    input logic [3:0] S,
    input logic       Cout
);

    // Combinational RTL is sampled on the formal global clock.
    
    // S must match the implemented XOR expression with Cin only on bit 0.
    check_sum_matches_rtl: assert property (
        @($global_clock) S == (A ^ B ^ {3'b000, Cin})
    );

    // Sum bit 0 includes the carry-in.
    check_sum_bit0_uses_cin: assert property (
        @($global_clock) S[0] == (A[0] ^ B[0] ^ Cin)
    );

    // Sum bits 3:1 ignore carry-in because the internal C[3:1] are tied low.
    check_sum_upper_bits_ignore_cin: assert property (
        @($global_clock) S[3:1] == (A[3:1] ^ B[3:1])
    );

    // Cout is the implemented LSB carry term after scalar truncation.
    check_cout_matches_implemented_lsb_carry: assert property (
        @($global_clock) Cout == ((A[0] & B[0]) | (Cin & (A[0] ^ B[0])))
    );

    // With Cin low, S reduces to A XOR B.
    check_sum_when_cin_zero: assert property (
        @($global_clock) (Cin == 1'b0) |-> (S == (A ^ B))
    );

    // With Cin low, Cout reduces to the LSB AND term.
    check_cout_when_cin_zero: assert property (
        @($global_clock) (Cin == 1'b0) |-> (Cout == (A[0] & B[0]))
    );

    // With Cin high, only S[0] is inverted relative to A XOR B.
    check_sum_when_cin_one: assert property (
        @($global_clock) (Cin == 1'b1) |-> (S == (A ^ B ^ 4'b0001))
    );

    // With Cin high, Cout reduces to the LSB OR term.
    check_cout_when_cin_one: assert property (
        @($global_clock) (Cin == 1'b1) |-> (Cout == (A[0] | B[0]))
    );

endmodule