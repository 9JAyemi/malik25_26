module sky130_fd_sc_ms__o32ai_sva (
    input logic CLK,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);
    // Precompute group ORs used by the O32AI boolean function
    logic a_or, b_or;
    assign a_or = (A1 | A2 | A3);
    assign b_or = (B1 | B2);

    ///// Functional equivalence /////
    // Y equals ~((A1|A2|A3) & (B1|B2)).
    check_boolean_function: assert property (
        @(posedge CLK) Y === ~(a_or & b_or)
    );

    ///// Output implications /////
    // If Y is LOW, the A-group OR must be HIGH.
    y_low_implies_a_group_or_high: assert property (
        @(posedge CLK) (Y === 1'b0) |-> (a_or === 1'b1)
    );
    // If Y is LOW, the B-group OR must be HIGH.
    y_low_implies_b_group_or_high: assert property (
        @(posedge CLK) (Y === 1'b0) |-> (b_or === 1'b1)
    );
    // If both group ORs are HIGH, Y must be LOW.
    both_groups_high_implies_y_low: assert property (
        @(posedge CLK) ((a_or === 1'b1) && (b_or === 1'b1)) |-> (Y === 1'b0)
    );
    // If all A inputs are LOW, Y must be HIGH.
    all_a_zero_implies_y_high: assert property (
        @(posedge CLK) ((A1 === 1'b0) && (A2 === 1'b0) && (A3 === 1'b0)) |-> (Y === 1'b1)
    );
    // If all B inputs are LOW, Y must be HIGH.
    all_b_zero_implies_y_high: assert property (
        @(posedge CLK) ((B1 === 1'b0) && (B2 === 1'b0)) |-> (Y === 1'b1)
    );
    // If Y is HIGH, not both group ORs can be HIGH.
    y_high_implies_not_both_groups_high: assert property (
        @(posedge CLK) (Y === 1'b1) |-> !((a_or === 1'b1) && (b_or === 1'b1))
    );

    ///// Robustness checks /////
    // When all inputs are known (no X/Z), Y must also be known.
    known_inputs_imply_known_output: assert property (
        @(posedge CLK) (!$isunknown({A1, A2, A3, B1, B2})) |-> !$isunknown(Y)
    );
    // If inputs are stable cycle-to-cycle, output must be stable.
    stable_inputs_imply_stable_output: assert property (
        @(posedge CLK) $stable({A1, A2, A3, B1, B2}) |-> $stable(Y)
    );

    ///// Representative minterms /////
    // If A1 and B1 are HIGH, Y must be LOW.
    a1_b1_implies_y_low: assert property (
        @(posedge CLK) ((A1 === 1'b1) && (B1 === 1'b1)) |-> (Y === 1'b0)
    );
    // If A2 and B1 are HIGH, Y must be LOW.
    a2_b1_implies_y_low: assert property (
        @(posedge CLK) ((A2 === 1'b1) && (B1 === 1'b1)) |-> (Y === 1'b0)
    );
    // If A3 and B2 are HIGH, Y must be LOW.
    a3_b2_implies_y_low: assert property (
        @(posedge CLK) ((A3 === 1'b1) && (B2 === 1'b1)) |-> (Y === 1'b0)
    );
endmodule