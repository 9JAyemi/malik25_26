module four_bit_adder_sva (
    input  logic        CLK,   // External assertion clock (RTL has no clock/reset)
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic        Cin,
    input  logic        Cout,
    input  logic [3:0]  S
);
    // Helper carry expressions derived from inputs (reflect RTL ripple structure)
    logic c0_e, c1_e, c2_e;
    assign c0_e = (A[0] & B[0]) | (Cin & (A[0] ^ B[0]));
    assign c1_e = (A[1] & B[1]) | (c0_e & (A[1] ^ B[1]));
    assign c2_e = (A[2] & B[2]) | (c1_e & (A[2] ^ B[2]));

    ///// Functional correctness of the adder /////
    // Concatenated {Cout,S} equals 5-bit arithmetic sum A + B + Cin.
    check_sum_matches_arithmetic: assert property (
        @(posedge CLK) disable iff (1'b0) {Cout, S} == (A + B + Cin)
    );
    // Bit 0 sum is XOR of A[0], B[0], and Cin.
    check_bit0_sum_xor: assert property (
        @(posedge CLK) disable iff (1'b0) S[0] == (A[0] ^ B[0] ^ Cin)
    );
    // Bit 1 sum is XOR of A[1], B[1], and carry from bit 0.
    check_bit1_sum_xor: assert property (
        @(posedge CLK) disable iff (1'b0) S[1] == (A[1] ^ B[1] ^ c0_e)
    );
    // Bit 2 sum is XOR of A[2], B[2], and carry from bit 1.
    check_bit2_sum_xor: assert property (
        @(posedge CLK) disable iff (1'b0) S[2] == (A[2] ^ B[2] ^ c1_e)
    );
    // Bit 3 sum is XOR of A[3], B[3], and carry from bit 2.
    check_bit3_sum_xor: assert property (
        @(posedge CLK) disable iff (1'b0) S[3] == (A[3] ^ B[3] ^ c2_e)
    );
    // Final carry-out equals carry function of bit 3 and carry from bit 2.
    check_cout_formula: assert property (
        @(posedge CLK) disable iff (1'b0) Cout == ((A[3] & B[3]) | (c2_e & (A[3] ^ B[3])))
    );

    ///// Basic identities and boundary cases /////
    // Adding zero B with Cin=0 passes A through and no carry.
    check_zero_identity_B: assert property (
        @(posedge CLK) disable iff (1'b0) ((B == 4'b0000) && (Cin == 1'b0)) |-> ((S == A) && (Cout == 1'b0))
    );
    // Adding zero A with Cin=0 passes B through and no carry.
    check_zero_identity_A: assert property (
        @(posedge CLK) disable iff (1'b0) ((A == 4'b0000) && (Cin == 1'b0)) |-> ((S == B) && (Cout == 1'b0))
    );
    // Only Cin=1 with A=0 and B=0 yields S=1 and Cout=0.
    check_cin_only: assert property (
        @(posedge CLK) disable iff (1'b0) ((A == 4'b0000) && (B == 4'b0000) && (Cin == 1'b1)) |-> ((S == 4'b0001) && (Cout == 1'b0))
    );
    // 0xF + 0x1 with Cin=0 wraps to 0x0 with Cout=1.
    check_overflow_F_plus_1: assert property (
        @(posedge CLK) disable iff (1'b0) ((A == 4'hF) && (B == 4'h1) && (Cin == 1'b0)) |-> ((S == 4'h0) && (Cout == 1'b1))
    );
    // 0xF + 0xF + Cin=1 yields 0xF with Cout=1.
    check_overflow_FF_plus_1: assert property (
        @(posedge CLK) disable iff (1'b0) ((A == 4'hF) && (B == 4'hF) && (Cin == 1'b1)) |-> ((S == 4'hF) && (Cout == 1'b1))
    );

    ///// Combinational stability /////
    // If inputs are stable across a cycle, outputs remain stable.
    check_output_stability_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (1'b0) $stable({A,B,Cin}) |-> $stable({S,Cout})
    );
endmodule