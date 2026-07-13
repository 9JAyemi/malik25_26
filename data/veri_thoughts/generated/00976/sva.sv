module adder_sva (
    input logic CLK,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic CIN,
    input logic [15:0] SUM,
    input logic COUT
);
    ///// Functional equivalence to RTL /////
    // SUM equals the 16-bit truncated result of A + B + CIN.
    check_sum_matches_add: assert property (
        @(posedge CLK) SUM == (A + B + CIN)
    );

    // COUT is always zero because the RHS sum is 16-bit and the MSB is zero-extended.
    check_cout_always_zero: assert property (
        @(posedge CLK) COUT == 1'b0
    );

    // {COUT,SUM} equals zero-extended 16-bit addition.
    check_concat_zeroext_add: assert property (
        @(posedge CLK) {COUT, SUM} == {1'b0, (A + B + CIN)}
    );

    ///// Basic pass-through scenarios /////
    // With B==0 and CIN==0, SUM passes A and COUT stays zero.
    check_pass_through_a: assert property (
        @(posedge CLK) (B == 16'h0000) && (CIN == 1'b0) |-> (SUM == A) && (COUT == 1'b0)
    );

    // With A==0 and CIN==0, SUM passes B and COUT stays zero.
    check_pass_through_b: assert property (
        @(posedge CLK) (A == 16'h0000) && (CIN == 1'b0) |-> (SUM == B) && (COUT == 1'b0)
    );

    // With A==0 and B==0, SUM equals CIN and COUT stays zero.
    check_only_cin: assert property (
        @(posedge CLK) (A == 16'h0000) && (B == 16'h0000) |-> (SUM == {15'b0, CIN}) && (COUT == 1'b0)
    );

    ///// Arithmetic identities preserved by 16-bit truncation /////
    // For two's-complement wraparound: A + ~A + 1 = 0 (truncated), so SUM==0 and COUT==0.
    check_twos_complement_cancel: assert property (
        @(posedge CLK) (B == ~A) && (CIN == 1'b1) |-> (SUM == 16'h0000) && (COUT == 1'b0)
    );

    ///// Bit-level consequence /////
    // LSB of SUM equals parity of LSBs and CIN for 16-bit addition.
    check_sum_bit0_parity: assert property (
        @(posedge CLK) SUM[0] == (A[0] ^ B[0] ^ CIN)
    );

    ///// Commutativity reflection /////
    // The computed SUM is commutative in A and B.
    check_sum_commutative: assert property (
        @(posedge CLK) (A + B + CIN) == (B + A + CIN)
    );

endmodule