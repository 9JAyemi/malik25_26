module sky130_fd_sc_hd__fa_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic CIN,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic COUT,
    input logic SUM
);

    // SUM is the XOR of A, B, and CIN.
    check_sum_xor: assert property (
        @(posedge clk) SUM == (A ^ B ^ CIN)
    );

    // COUT matches the carry logic implemented in the RTL.
    check_cout_logic: assert property (
        @(posedge clk) COUT == ((A & B) | (CIN & (A ^ B)))
    );

    // The outputs together equal the 2-bit sum of the three 1-bit inputs.
    check_full_adder_result: assert property (
        @(posedge clk) {COUT, SUM} == ({1'b0, A} + {1'b0, B} + {1'b0, CIN})
    );

    // When A and B are equal, SUM follows CIN.
    check_sum_matches_cin_when_ab_equal: assert property (
        @(posedge clk) (!(A ^ B)) |-> (SUM == CIN)
    );

    // When A and B differ, SUM is the inverse of CIN.
    check_sum_inverts_cin_when_ab_differs: assert property (
        @(posedge clk) (A ^ B) |-> (SUM == ~CIN)
    );

    // With CIN low, carry reduces to A AND B.
    check_cout_reduces_to_and_when_cin_low: assert property (
        @(posedge clk) (!CIN) |-> (COUT == (A & B))
    );

    // With CIN high, carry reduces to A OR B.
    check_cout_reduces_to_or_when_cin_high: assert property (
        @(posedge clk) CIN |-> (COUT == (A | B))
    );

    // If both A and B are low, carry must be low.
    check_cout_low_when_ab_low: assert property (
        @(posedge clk) ((!A) && (!B)) |-> (!COUT)
    );

    // If both A and B are high, carry must be high.
    check_cout_high_when_ab_high: assert property (
        @(posedge clk) (A && B) |-> COUT
    );

endmodule