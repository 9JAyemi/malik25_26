module sky130_fd_sc_lp__o32ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);

    // Y matches the implemented OR-of-NOR function.
    check_truth_function: assert property (
        @(posedge clk)
        Y == ((!A1 && !A2 && !A3) || (!B1 && !B2))
    );

    // If all A inputs are low, the A-side NOR forces Y high.
    check_all_a_low_sets_y_high: assert property (
        @(posedge clk)
        (!A1 && !A2 && !A3) |-> Y
    );

    // If both B inputs are low, the B-side NOR forces Y high.
    check_all_b_low_sets_y_high: assert property (
        @(posedge clk)
        (!B1 && !B2) |-> Y
    );

    // If any A input and any B input are high, Y must be low.
    check_a_and_b_activity_sets_y_low: assert property (
        @(posedge clk)
        ((A1 || A2 || A3) && (B1 || B2)) |-> !Y
    );

    // A low Y requires at least one asserted A-side input.
    check_y_low_implies_a_activity: assert property (
        @(posedge clk)
        !Y |-> (A1 || A2 || A3)
    );

    // A low Y requires at least one asserted B-side input.
    check_y_low_implies_b_activity: assert property (
        @(posedge clk)
        !Y |-> (B1 || B2)
    );

    // If Y is high while any A input is high, both B inputs must be low.
    check_y_high_with_a_activity_requires_b_low: assert property (
        @(posedge clk)
        (Y && (A1 || A2 || A3)) |-> (!B1 && !B2)
    );

    // If Y is high while any B input is high, all A inputs must be low.
    check_y_high_with_b_activity_requires_a_low: assert property (
        @(posedge clk)
        (Y && (B1 || B2)) |-> (!A1 && !A2 && !A3)
    );

endmodule