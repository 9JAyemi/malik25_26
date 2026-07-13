module sky130_fd_sc_ms__fahcin_sva (
    input logic CLK,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CIN
);
    ///// Functional equivalence to gate-level logic /////
    // SUM equals 3-input XOR of A, B, and ~CIN.
    check_sum_eq_xor3_inv_cin: assert property (
        @(posedge CLK) disable iff (1'b0) SUM == (A ^ B ^ (~CIN))
    );
    // COUT equals (A & B) | (A & ~CIN) | (B & ~CIN).
    check_cout_eq_or3_of_ands: assert property (
        @(posedge CLK) disable iff (1'b0) COUT == ((A & B) | (A & (~CIN)) | (B & (~CIN)))
    );

    ///// Derived behaviors for CIN = 1 /////
    // When CIN=1, SUM reduces to A ^ B.
    check_sum_when_cin_1: assert property (
        @(posedge CLK) disable iff (1'b0) (CIN == 1'b1) |-> (SUM == (A ^ B))
    );
    // When CIN=1, COUT reduces to A & B.
    check_cout_when_cin_1: assert property (
        @(posedge CLK) disable iff (1'b0) (CIN == 1'b1) |-> (COUT == (A & B))
    );

    ///// Derived behaviors for CIN = 0 /////
    // When CIN=0, SUM reduces to ~(A ^ B).
    check_sum_when_cin_0: assert property (
        @(posedge CLK) disable iff (1'b0) (CIN == 1'b0) |-> (SUM == ~(A ^ B))
    );
    // When CIN=0, COUT reduces to A | B.
    check_cout_when_cin_0: assert property (
        @(posedge CLK) disable iff (1'b0) (CIN == 1'b0) |-> (COUT == (A | B))
    );

    ///// Partition by A == B vs A != B /////
    // If A == B, SUM equals ~CIN.
    check_sum_when_a_eq_b: assert property (
        @(posedge CLK) disable iff (1'b0) (A == B) |-> (SUM == (~CIN))
    );
    // If A == B, COUT equals A (same as A & B).
    check_cout_when_a_eq_b: assert property (
        @(posedge CLK) disable iff (1'b0) (A == B) |-> (COUT == A)
    );
    // If A != B, SUM equals CIN.
    check_sum_when_a_neq_b: assert property (
        @(posedge CLK) disable iff (1'b0) (A != B) |-> (SUM == CIN)
    );
    // If A != B, COUT equals ~CIN.
    check_cout_when_a_neq_b: assert property (
        @(posedge CLK) disable iff (1'b0) (A != B) |-> (COUT == (~CIN))
    );
endmodule