module sky130_fd_sc_ms__o221ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // Y equals NAND3 of (A1|A2), (B1|B2), and C1.
    check_func_nand_of_ors: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge B2 or posedge C1)
        Y === ~(((A1 | A2) & (B1 | B2) & C1))
    );

    // C1 low forces Y high.
    check_c1_low_forces_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge B2 or posedge C1)
        (C1 == 1'b0) |-> (Y == 1'b1)
    );

    // Both A inputs low force Y high.
    check_a_pair_zero_forces_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge B2 or posedge C1)
        ((A1 == 1'b0) && (A2 == 1'b0)) |-> (Y == 1'b1)
    );

    // Both B inputs low force Y high.
    check_b_pair_zero_forces_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge B2 or posedge C1)
        ((B1 == 1'b0) && (B2 == 1'b0)) |-> (Y == 1'b1)
    );

    // When (A1|A2) and (B1|B2) and C1 are all high, Y is low.
    check_all_terms_high_forces_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge B2 or posedge C1)
        ((C1 == 1'b1) && (A1 || A2) && (B1 || B2)) |-> (Y == 1'b0)
    );

    // Y low implies (A1|A2)=1, (B1|B2)=1, and C1=1.
    check_y_low_implies_all_terms_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge B2 or posedge C1)
        (Y == 1'b0) |-> ((C1 == 1'b1) && (A1 || A2) && (B1 || B2))
    );

    // Y high implies at least one of (A1|A2), (B1|B2), or C1 is low.
    check_y_high_implies_some_term_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge B2 or posedge C1)
        (Y == 1'b1) |-> ((C1 == 1'b0) || ((A1 == 1'b0) && (A2 == 1'b0)) || ((B1 == 1'b0) && (B2 == 1'b0)))
    );

    // With C1=1 and (B1|B2)=1, Y equals ~(A1|A2).
    check_dep_on_A_when_BC_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge B2 or posedge C1)
        ((C1 == 1'b1) && (B1 || B2)) |-> (Y === ~(A1 | A2))
    );

    // With C1=1 and (A1|A2)=1, Y equals ~(B1|B2).
    check_dep_on_B_when_AC_high: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge B2 or posedge C1)
        ((C1 == 1'b1) && (A1 || A2)) |-> (Y === ~(B1 | B2))
    );

    // All inputs high force Y low.
    check_all_ones_forces_low: assert property (
        @(posedge A1 or posedge A2 or posedge B1 or posedge B2 or posedge C1)
        ((A1 == 1'b1) && (A2 == 1'b1) && (B1 == 1'b1) && (B2 == 1'b1) && (C1 == 1'b1)) |-> (Y == 1'b0)
    );

endmodule