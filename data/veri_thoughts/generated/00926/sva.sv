module three_input_gate_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

    ///// Functional equivalence /////
    // Y must equal B1 | (A1 & A2) after any input/output edge.
    check_functional_equivalence: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge Y or negedge Y)
            ##0 (Y == (B1 | (A1 & A2)))
    );

    ///// Implications from inputs /////
    // If B1 is HIGH, Y must be HIGH after settle.
    check_b1_high_forces_y1: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge Y or negedge Y)
            ##0 (B1 == 1'b1) |-> (Y == 1'b1)
    );
    // If both A1 and A2 are HIGH, Y must be HIGH after settle.
    check_a_pair_high_forces_y1: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge Y or negedge Y)
            ##0 ((A1 == 1'b1) && (A2 == 1'b1)) |-> (Y == 1'b1)
    );
    // If B1 is LOW and any of A1/A2 is LOW, Y must be LOW after settle.
    check_b1_low_and_any_a_low_forces_y0: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge Y or negedge Y)
            ##0 ((B1 == 1'b0) && ((A1 == 1'b0) || (A2 == 1'b0))) |-> (Y == 1'b0)
    );

    ///// Implications from output /////
    // If Y is LOW, then B1 is LOW and at least one of A1/A2 is LOW.
    check_y0_implies_inputs: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge Y or negedge Y)
            ##0 (Y == 1'b0) |-> ((B1 == 1'b0) && ((A1 == 1'b0) || (A2 == 1'b0)))
    );
    // If Y is HIGH, then B1 is HIGH or both A1 and A2 are HIGH.
    check_y1_implies_inputs: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge Y or negedge Y)
            ##0 (Y == 1'b1) |-> ((B1 == 1'b1) || ((A1 == 1'b1) && (A2 == 1'b1)))
    );

    ///// Edge-specific settle checks /////
    // On B1 rising edge, Y must be HIGH after delta.
    check_posedge_b1_sets_y1: assert property (
        @(posedge B1) ##0 (Y == 1'b1)
    );
    // On B1 falling edge, Y must equal A1 & A2 after delta.
    check_negedge_b1_sets_y_and: assert property (
        @(negedge B1) ##0 (Y == (A1 & A2))
    );
    // On A1 rising edge, Y must equal B1 | A2 after delta.
    check_posedge_a1_updates_y: assert property (
        @(posedge A1) ##0 (Y == (B1 | A2))
    );
    // On A1 falling edge, Y must equal B1 after delta.
    check_negedge_a1_updates_y: assert property (
        @(negedge A1) ##0 (Y == B1)
    );
    // On A2 rising edge, Y must equal B1 | A1 after delta.
    check_posedge_a2_updates_y: assert property (
        @(posedge A2) ##0 (Y == (B1 | A1))
    );
    // On A2 falling edge, Y must equal B1 after delta.
    check_negedge_a2_updates_y: assert property (
        @(negedge A2) ##0 (Y == B1)
    );

endmodule