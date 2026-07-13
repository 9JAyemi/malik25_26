module sky130_fd_sc_lp__fahcin_sva (
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CIN
);
    // Combinational DUT with no clock/reset; sample properties on $global_clock.
    default clocking cb @(posedge $global_clock); endclocking

    ///// Functional equivalence to gate-level logic /////
    // SUM equals A ^ B ^ ~CIN.
    check_sum_functional: assert property ( SUM == (A ^ B ^ ~CIN) );

    // COUT equals (A&B) | (A&~CIN) | (B&~CIN).
    check_cout_functional: assert property ( COUT == ((A & B) | (A & ~CIN) | (B & ~CIN)) );

    ///// Behavior conditioned on CIN /////
    // When CIN is 0, SUM is bitwise NOT of A^B.
    check_sum_when_cin0: assert property ( (CIN == 1'b0) |-> (SUM == ~(A ^ B)) );

    // When CIN is 1, SUM equals A^B.
    check_sum_when_cin1: assert property ( (CIN == 1'b1) |-> (SUM == (A ^ B)) );

    // When CIN is 0, COUT equals A|B.
    check_cout_when_cin0: assert property ( (CIN == 1'b0) |-> (COUT == (A | B)) );

    // When CIN is 1, COUT equals A&B.
    check_cout_when_cin1: assert property ( (CIN == 1'b1) |-> (COUT == (A & B)) );

    ///// Behavior conditioned on A/B relation /////
    // When A equals B, SUM equals ~CIN.
    check_sum_when_a_eq_b: assert property ( (A == B) |-> (SUM == ~CIN) );

    // When A differs from B, SUM equals CIN.
    check_sum_when_a_neq_b: assert property ( (A ^ B) |-> (SUM == CIN) );

    // When A equals B, COUT equals A.
    check_cout_when_a_eq_b: assert property ( (A == B) |-> (COUT == A) );

    // When A differs from B, COUT equals ~CIN.
    check_cout_when_a_neq_b: assert property ( (A ^ B) |-> (COUT == ~CIN) );

endmodule