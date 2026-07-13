module sky130_fd_sc_hdll__a221oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);
    // Y equals ~(C1 | (A1&A2) | (B1&B2)).
    check_function_equivalence: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        Y == ~((A1 & A2) | (B1 & B2) | C1)
    );

    // If C1 is HIGH, Y must be LOW.
    check_c1_high_forces_y_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        C1 |-> (Y == 1'b0)
    );

    // If A1&A2 is HIGH, Y must be LOW.
    check_a_pair_high_forces_y_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (A1 & A2) |-> (Y == 1'b0)
    );

    // If B1&B2 is HIGH, Y must be LOW.
    check_b_pair_high_forces_y_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (B1 & B2) |-> (Y == 1'b0)
    );

    // If no term is asserted, Y must be HIGH.
    check_no_terms_high_gives_y_high: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (!C1 && !(A1 & A2) && !(B1 & B2)) |-> (Y == 1'b1)
    );

    // Y HIGH implies C1 is LOW and neither pair is both HIGH.
    check_y_high_implies_terms_low: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (Y == 1'b1) |-> (!C1 && !(A1 & A2) && !(B1 & B2))
    );

    // Y LOW implies at least one term is asserted.
    check_y_low_implies_some_term_high: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (Y == 1'b0) |-> (C1 || (A1 & A2) || (B1 & B2))
    );

    // When both pairs are not simultaneously HIGH, Y equals ~C1.
    check_pairs_not_both_high_reduce_to_not_c1: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (!(A1 & A2) && !(B1 & B2)) |-> (Y == ~C1)
    );

    // When C1 is LOW, Y equals ~((A1&A2) | (B1&B2)).
    check_c1_low_reduces_to_nor_of_ands: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (!C1) |-> (Y == ~((A1 & A2) | (B1 & B2)))
    );

    // All inputs LOW implies Y is HIGH.
    check_all_inputs_low_implies_y_high: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        ((A1 == 1'b0) && (A2 == 1'b0) && (B1 == 1'b0) && (B2 == 1'b0) && (C1 == 1'b0)) |-> (Y == 1'b1)
    );
endmodule