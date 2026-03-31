module sky130_fd_sc_ms__a221oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);
    // No clock/reset in RTL; pure combinational a221oi gate.
    // Assertions sample on any input edge (posedge/negedge of A1/A2/B1/B2/C1).
    // Function: Y = ~((A1 & A2) | (B1 & B2) | C1).

    // Core Boolean equation for the cell.
    check_boolean_equation: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        Y == ~((A1 & A2) | (B1 & B2) | C1)
    );

    // C1 high forces Y low.
    check_C1_high_forces_Y_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (C1 == 1'b1) |-> (Y == 1'b0)
    );

    // A1&A2 high forces Y low.
    check_A_pair_high_forces_Y_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        ((A1 & A2) == 1'b1) |-> (Y == 1'b0)
    );

    // B1&B2 high forces Y low.
    check_B_pair_high_forces_Y_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        ((B1 & B2) == 1'b1) |-> (Y == 1'b0)
    );

    // When all terms are false, Y is high.
    check_no_terms_true_gives_Y_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (((A1 & A2) == 1'b0) && ((B1 & B2) == 1'b0) && (C1 == 1'b0)) |-> (Y == 1'b1)
    );

    // Y high implies all terms are false.
    check_Y_high_implies_no_true_terms: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (Y == 1'b1) |-> (((A1 & A2) == 1'b0) && ((B1 & B2) == 1'b0) && (C1 == 1'b0))
    );

    // Y low implies at least one term is true.
    check_Y_low_implies_some_true_term: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (Y == 1'b0) |-> (((A1 & A2) == 1'b1) || ((B1 & B2) == 1'b1) || (C1 == 1'b1))
    );

    // Rising C1 drives Y low in the same sample.
    check_rose_C1_forces_Y_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        $rose(C1) |-> (Y == 1'b0)
    );

    // Rising (A1&A2) drives Y low in the same sample.
    check_rose_Apair_forces_Y_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        $rose(A1 & A2) |-> (Y == 1'b0)
    );

    // Rising (B1&B2) drives Y low in the same sample.
    check_rose_Bpair_forces_Y_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        $rose(B1 & B2) |-> (Y == 1'b0)
    );

    // Falling of ((A1&A2)|(B1&B2)|C1) drives Y high in the same sample.
    check_fell_any_term_clears_Y: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        $fell((A1 & A2) | (B1 & B2) | C1) |-> (Y == 1'b1)
    );
endmodule