module binary_adder_sva (
    // External sampling clock/reset for SVA (DUT is purely combinational)
    input logic clk,
    input logic reset_n,
    // DUT ports
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [3:0] S,
    input logic COUT
);
    // DUT has no clock/reset; logic is purely combinational. Assertions sample on clk.

    // Local aliases for carry chain and 5-bit sum
    let c0   = (A[0] & B[0]) | (A[0] & CIN) | (B[0] & CIN);
    let c1   = (A[1] & B[1]) | (A[1] & c0)  | (B[1] & c0);
    let c2   = (A[2] & B[2]) | (A[2] & c1)  | (B[2] & c1);
    let sum5 = {1'b0, A} + {1'b0, B} + CIN;

    ///// Functional equivalence /////
    // 5-bit result equals A + B + CIN.
    check_full_sum_equivalence: assert property (
        @(posedge clk) disable iff (!reset_n) {COUT, S} == sum5
    );

    ///// Bit-level ripple-carry equations /////
    // Bit 0 sum is XOR of A[0], B[0], CIN.
    check_bit0_sum_xor: assert property (
        @(posedge clk) disable iff (!reset_n) S[0] == (A[0] ^ B[0] ^ CIN)
    );
    // Bit 1 sum uses carry from bit 0.
    check_bit1_sum_xor_with_c0: assert property (
        @(posedge clk) disable iff (!reset_n) S[1] == (A[1] ^ B[1] ^ c0)
    );
    // Bit 2 sum uses carry from bit 1.
    check_bit2_sum_xor_with_c1: assert property (
        @(posedge clk) disable iff (!reset_n) S[2] == (A[2] ^ B[2] ^ c1)
    );
    // Bit 3 sum uses carry from bit 2.
    check_bit3_sum_xor_with_c2: assert property (
        @(posedge clk) disable iff (!reset_n) S[3] == (A[3] ^ B[3] ^ c2)
    );
    // Final carry-out from bit 3 matches generate/propagate logic.
    check_cout_from_c2: assert property (
        @(posedge clk) disable iff (!reset_n) COUT == ((A[3] & B[3]) | (A[3] & c2) | (B[3] & c2))
    );

    ///// Sanity behaviors (direct consequences of the adder logic) /////
    // When B==0 and CIN==0, output equals A with no carry.
    check_transparent_when_B_zero_no_cin: assert property (
        @(posedge clk) disable iff (!reset_n) ((B == 4'b0) && (CIN == 1'b0)) |-> (S == A && COUT == 1'b0)
    );
    // When A==0 and CIN==0, output equals B with no carry.
    check_transparent_when_A_zero_no_cin: assert property (
        @(posedge clk) disable iff (!reset_n) ((A == 4'b0) && (CIN == 1'b0)) |-> (S == B && COUT == 1'b0)
    );
    // All zeros in yields all zeros out.
    check_zero_inputs_zero_outputs: assert property (
        @(posedge clk) disable iff (!reset_n) ((A == 4'b0) && (B == 4'b0) && (CIN == 1'b0)) |-> ((S == 4'b0) && (COUT == 1'b0))
    );
    // Only CIN asserted increments by 1 with no carry-out.
    check_only_cin_increments_by_one: assert property (
        @(posedge clk) disable iff (!reset_n) ((A == 4'b0) && (B == 4'b0) && (CIN == 1'b1)) |-> ((S == 4'b0001) && (COUT == 1'b0))
    );
endmodule