module my_module_name_assertions (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1
);

    // Y matches the implemented NOR-of-terms function.
    check_y_matches_boolean_function: assert property (
        @(posedge clk) Y == ~((B1 & B2) | C1 | (A1 & A2))
    );

    // C1 asserted forces Y low.
    check_c1_forces_y_low: assert property (
        @(posedge clk) C1 |-> !Y
    );

    // A1 and A2 both asserted force Y low.
    check_a_pair_forces_y_low: assert property (
        @(posedge clk) (A1 && A2) |-> !Y
    );

    // B1 and B2 both asserted force Y low.
    check_b_pair_forces_y_low: assert property (
        @(posedge clk) (B1 && B2) |-> !Y
    );

    // With no active NOR input term, Y must be high.
    check_no_active_term_sets_y_high: assert property (
        @(posedge clk) (!C1 && !(A1 && A2) && !(B1 && B2)) |-> Y
    );

    // If Y is low, at least one NOR input term must be active.
    check_y_low_has_active_cause: assert property (
        @(posedge clk) !Y |-> (C1 || (A1 && A2) || (B1 && B2))
    );

    // If Y is high, all NOR input terms must be inactive.
    check_y_high_means_all_terms_inactive: assert property (
        @(posedge clk) Y |-> (!C1 && !(A1 && A2) && !(B1 && B2))
    );

endmodule