module logical_gate_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);
    // No clock/reset in RTL; pure combinational. Sample on any input/output edge.

    // Y equals the intended OR-of-ANDs function.
    check_function_equivalence: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge Y or negedge Y)
            (Y == ((A1 & A2) | (B1 & B2)))
    );

    // If Y is HIGH then at least one AND term is HIGH.
    check_y_high_implies_term_true: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge Y or negedge Y)
            (Y) |-> ((A1 & A2) | (B1 & B2))
    );

    // If Y is LOW then neither AND term is HIGH.
    check_y_low_implies_terms_false: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge Y or negedge Y)
            (!Y) |-> !((A1 & A2) | (B1 & B2))
    );

    // A-term HIGH forces Y HIGH.
    check_a_term_forces_y_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge Y or negedge Y)
            ((A1 & A2)) |-> (Y)
    );

    // B-term HIGH forces Y HIGH.
    check_b_term_forces_y_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge Y or negedge Y)
            ((B1 & B2)) |-> (Y)
    );

    // If both first inputs are LOW, Y must be LOW.
    check_first_inputs_both_low_force_y_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge Y or negedge Y)
            ((!A1) && (!B1)) |-> (!Y)
    );

    // If both second inputs are LOW, Y must be LOW.
    check_second_inputs_both_low_force_y_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge B2 or negedge B2 or posedge Y or negedge Y)
            ((!A2) && (!B2)) |-> (!Y)
    );

    // On a rising edge of Y, at least one AND term is HIGH.
    check_y_rise_requires_term_true: assert property (
        @(posedge Y) ((A1 & A2) | (B1 & B2))
    );

    // On a falling edge of Y, both AND terms are not HIGH.
    check_y_fall_requires_terms_false: assert property (
        @(negedge Y) !((A1 & A2) | (B1 & B2))
    );

endmodule