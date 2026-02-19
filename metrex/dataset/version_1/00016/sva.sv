module nand_adder_4bit_sva (
    // External clock for sampling assertions (DUT is purely combinational)
    input  logic        CLK,

    // DUT ports (treated as inputs to this checker)
    input  logic [3:0]  S,
    input  logic        C_out,
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic        C_in
);
    ////////////////////////////////////////////////////////////////////////////////
    // Analysis summary:
    // - Clocks/Resets in RTL: None. The DUT is purely combinational; no reset.
    // - Logic type: Combinational (a chain of 1-bit full adders built from NANDs).
    // - Key behavior: 4-bit ripple-carry addition of A and B with carry-in C_in.
    //   Outputs are S (sum[3:0]) and C_out (final carry).
    // - This SVA module introduces an external CLK for property sampling only.
    ////////////////////////////////////////////////////////////////////////////////

    // Reference computations for assertions
    function automatic logic carry_next (input logic x, input logic y, input logic cin);
        carry_next = (x & y) | (x & cin) | (y & cin);
    endfunction

    // Derived carry chain from inputs (pure combinational reference model)
    logic c0_ref, c1_ref, c2_ref, c3_ref;
    assign c0_ref = carry_next(A[0], B[0], C_in);
    assign c1_ref = carry_next(A[1], B[1], c0_ref);
    assign c2_ref = carry_next(A[2], B[2], c1_ref);
    assign c3_ref = carry_next(A[3], B[3], c2_ref);

    // 5-bit reference sum (explicitly sized to avoid truncation)
    logic [4:0] sum5_ref;
    assign sum5_ref = {1'b0, A} + {1'b0, B} + {4'b0000, C_in};

    ///// Functional correctness /////
    // The 5-bit output {C_out,S} must equal the 5-bit addition of A, B, and C_in.
    check_addition_equivalence: assert property (
        @(posedge CLK) {C_out, S} == sum5_ref
    );

    // The carry-out must equal the MSB of the 5-bit addition result.
    check_cout_matches_addition_msb: assert property (
        @(posedge CLK) C_out == sum5_ref[4]
    );

    // The 4-bit sum S must equal the low 4 bits of the 5-bit addition result.
    check_sum_matches_addition_low4: assert property (
        @(posedge CLK) S == sum5_ref[3:0]
    );

    ///// Bit-level ripple-carry structure checks /////
    // Bit 0 sum is XOR of A[0], B[0], and C_in.
    check_sum_bit0_xor: assert property (
        @(posedge CLK) S[0] == (A[0] ^ B[0] ^ C_in)
    );

    // Bit 1 sum is XOR of A[1], B[1], and carry from bit 0.
    check_sum_bit1_xor_with_c0: assert property (
        @(posedge CLK) S[1] == (A[1] ^ B[1] ^ c0_ref)
    );

    // Bit 2 sum is XOR of A[2], B[2], and carry from bit 1.
    check_sum_bit2_xor_with_c1: assert property (
        @(posedge CLK) S[2] == (A[2] ^ B[2] ^ c1_ref)
    );

    // Bit 3 sum is XOR of A[3], B[3], and carry from bit 2.
    check_sum_bit3_xor_with_c2: assert property (
        @(posedge CLK) S[3] == (A[3] ^ B[3] ^ c2_ref)
    );

    // Final carry-out equals the carry generated from bit 3.
    check_cout_matches_c3: assert property (
        @(posedge CLK) C_out == c3_ref
    );

    ///// Stability (combinational behavior) /////
    // If inputs are stable across a cycle, outputs must also be stable.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable({A, B, C_in}) |-> $stable({S, C_out})
    );

    ///// Useful corner cases /////
    // Adding zero B with C_in=0 passes A through to S and keeps C_out=0.
    check_passthrough_when_B_zero_cin0: assert property (
        @(posedge CLK) ((B == 4'b0000) && (C_in == 1'b0)) |-> ((S == A) && (C_out == 1'b0))
    );

    // Adding zero A with C_in=0 passes B through to S and keeps C_out=0.
    check_passthrough_when_A_zero_cin0: assert property (
        @(posedge CLK) ((A == 4'b0000) && (C_in == 1'b0)) |-> ((S == B) && (C_out == 1'b0))
    );

    // When both A and B are zero, S equals C_in in bit[0] and zeros elsewhere; C_out is zero.
    check_when_A_B_zero: assert property (
        @(posedge CLK) ((A == 4'b0000) && (B == 4'b0000)) |-> ((S == {3'b000, C_in}) && (C_out == 1'b0))
    );

endmodule