module bitwise_full_adder_sva (
    input logic A,
    input logic B,
    input logic CIN,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB,
    input logic COUT,
    input logic SUM
);

    ///// Combinational full-adder function /////
    // SUM equals XOR of inputs.
    check_sum_definition: assert property (
        @(posedge A or posedge B or posedge CIN) disable iff (1'b0)
            SUM == (A ^ B) ^ CIN
    );

    // COUT equals carry function (A&B) | (CIN & (A^B)).
    check_cout_definition_impl: assert property (
        @(posedge A or posedge B or posedge CIN) disable iff (1'b0)
            COUT == ((A & B) | (CIN & (A ^ B)))
    );

    // COUT equals majority of inputs.
    check_cout_majority_equiv: assert property (
        @(posedge A or posedge B or posedge CIN) disable iff (1'b0)
            COUT == ((A & B) | (A & CIN) | (B & CIN))
    );

    ///// Truth-table spot checks /////
    // 0+0+0 -> SUM=0, COUT=0.
    check_case_000: assert property (
        @(posedge A or posedge B or posedge CIN) disable iff (1'b0)
            (!A && !B && !CIN) |-> (SUM == 1'b0 && COUT == 1'b0)
    );

    // Exactly one '1' -> SUM=1, COUT=0.
    check_case_popcount1: assert property (
        @(posedge A or posedge B or posedge CIN) disable iff (1'b0)
            ((A + B + CIN) == 1) |-> (SUM == 1'b1 && COUT == 1'b0)
    );

    // Exactly two '1's -> SUM=0, COUT=1.
    check_case_popcount2: assert property (
        @(posedge A or posedge B or posedge CIN) disable iff (1'b0)
            ((A + B + CIN) == 2) |-> (SUM == 1'b0 && COUT == 1'b1)
    );

    // 1+1+1 -> SUM=1, COUT=1.
    check_case_111: assert property (
        @(posedge A or posedge B or posedge CIN) disable iff (1'b0)
            (A && B && CIN) |-> (SUM == 1'b1 && COUT == 1'b1)
    );

    ///// Simple carry implications /////
    // If A&B then COUT must be 1.
    check_carry_when_ab: assert property (
        @(posedge A or posedge B or posedge CIN) disable iff (1'b0)
            (A && B) |-> (COUT == 1'b1)
    );

    // If A&CIN then COUT must be 1.
    check_carry_when_acin: assert property (
        @(posedge A or posedge B or posedge CIN) disable iff (1'b0)
            (A && CIN) |-> (COUT == 1'b1)
    );

    // If B&CIN then COUT must be 1.
    check_carry_when_bcin: assert property (
        @(posedge A or posedge B or posedge CIN) disable iff (1'b0)
            (B && CIN) |-> (COUT == 1'b1)
    );

    ///// XOR identities for SUM /////
    // If B==CIN then SUM==A.
    check_sum_when_b_eq_cin: assert property (
        @(posedge A or posedge B or posedge CIN) disable iff (1'b0)
            (B == CIN) |-> (SUM == A)
    );

    // If A==B then SUM==CIN.
    check_sum_when_a_eq_b: assert property (
        @(posedge A or posedge B or posedge CIN) disable iff (1'b0)
            (A == B) |-> (SUM == CIN)
    );

    // If A==CIN then SUM==B.
    check_sum_when_a_eq_cin: assert property (
        @(posedge A or posedge B or posedge CIN) disable iff (1'b0)
            (A == CIN) |-> (SUM == B)
    );

endmodule