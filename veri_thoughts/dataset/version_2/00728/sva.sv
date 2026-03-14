module o221a_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);
    // No clock/reset; purely combinational: X = (B2|B1) & (A2|A1) & C1.

    // X implements (B2|B1)&(A2|A1)&C1 on any input edge.
    check_function_equivalence_any_edge: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        X == ((B2 | B1) & (A2 | A1) & C1)
    );

    // If C1 is 0 then X must be 0.
    gating_c1_zero_forces_x_zero: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (C1 == 1'b0) |-> (X == 1'b0)
    );

    // If both A inputs are 0 then X must be 0.
    gating_a_pair_zero_forces_x_zero: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        ((A1 == 1'b0) && (A2 == 1'b0)) |-> (X == 1'b0)
    );

    // If both B inputs are 0 then X must be 0.
    gating_b_pair_zero_forces_x_zero: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        ((B1 == 1'b0) && (B2 == 1'b0)) |-> (X == 1'b0)
    );

    // If X is 1 then C1 must be 1.
    x_one_implies_c1_one: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (X == 1'b1) |-> (C1 == 1'b1)
    );

    // If X is 1 then at least one of A1/A2 is 1.
    x_one_implies_a_pair_one: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (X == 1'b1) |-> ((A1 | A2) == 1'b1)
    );

    // If X is 1 then at least one of B1/B2 is 1.
    x_one_implies_b_pair_one: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (X == 1'b1) |-> ((B1 | B2) == 1'b1)
    );

    // If all three conditions are met then X must be 1.
    sufficient_conditions_for_x_one: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (((B2 | B1) == 1'b1) && ((A2 | A1) == 1'b1) && (C1 == 1'b1)) |-> (X == 1'b1)
    );

    // If X is 0 then at least one AND input term must be 0.
    x_zero_implies_some_term_zero: assert property (
        @(posedge A1 or negedge A1 or
          posedge A2 or negedge A2 or
          posedge B1 or negedge B1 or
          posedge B2 or negedge B2 or
          posedge C1 or negedge C1)
        (X == 1'b0) |-> ((C1 == 1'b0) || ((A2 | A1) == 1'b0) || ((B2 | B1) == 1'b0))
    );

    // On a rising edge of X, all three enabling conditions must be true.
    x_rise_requires_all_high: assert property (
        @(posedge X) ((B2 | B1) == 1'b1) && ((A2 | A1) == 1'b1) && (C1 == 1'b1)
    );

    // On a falling edge of X, at least one enabling condition must be false.
    x_fall_requires_some_low: assert property (
        @(negedge X) ((C1 == 1'b0) || ((A2 | A1) == 1'b0) || ((B2 | B1) == 1'b0))
    );

endmodule