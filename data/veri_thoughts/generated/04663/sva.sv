module my_module_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1,
    input logic X
);

    // X implements B1 OR the 4-input AND of A1-A4.
    check_x_matches_function: assert property (
        @(posedge clk) X == (B1 || (A1 && A2 && A3 && A4))
    );

    // B1 being high is sufficient to drive X high.
    check_b1_forces_x_high: assert property (
        @(posedge clk) B1 |-> X
    );

    // All four A inputs high is sufficient to drive X high.
    check_all_a_high_forces_x_high: assert property (
        @(posedge clk) (A1 && A2 && A3 && A4) |-> X
    );

    // With B1 low, any low A input forces X low.
    check_no_b1_and_any_a_low_forces_x_low: assert property (
        @(posedge clk) (!B1 && (!A1 || !A2 || !A3 || !A4)) |-> !X
    );

    // If X is high, it must come from B1 or the 4-input AND.
    check_x_high_implies_valid_source: assert property (
        @(posedge clk) X |-> (B1 || (A1 && A2 && A3 && A4))
    );

    // If X is low, B1 is low and the 4-input AND is not satisfied.
    check_x_low_implies_no_valid_source: assert property (
        @(posedge clk) !X |-> (!B1 && (!A1 || !A2 || !A3 || !A4))
    );

endmodule