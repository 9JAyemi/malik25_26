module sky130_fd_sc_hvl__nor2_sva (
    input logic clk,   // external sampling clock (DUT has no clock/reset)
    input logic Y,
    input logic A,
    input logic B
);
    // Y equals logical NOR of A and B.
    check_y_equals_nor: assert property (
        @(posedge clk) Y == (~(A | B))
    );

    // If A is 1, Y must be 0.
    check_y_zero_when_a_one: assert property (
        @(posedge clk) (A == 1'b1) |-> (Y == 1'b0)
    );

    // If B is 1, Y must be 0.
    check_y_zero_when_b_one: assert property (
        @(posedge clk) (B == 1'b1) |-> (Y == 1'b0)
    );

    // If both A and B are 0, Y must be 1.
    check_y_one_when_both_zero: assert property (
        @(posedge clk) (!A && !B) |-> (Y == 1'b1)
    );

    // Y high implies both inputs are 0.
    check_y_high_implies_inputs_zero: assert property (
        @(posedge clk) (Y == 1'b1) |-> (!A && !B)
    );

    // Y can only rise when both inputs are 0.
    check_y_rise_requires_both_zero: assert property (
        @(posedge clk) $rose(Y) |-> (!A && !B)
    );

    // Y can only fall when at least one input is 1.
    check_y_fall_requires_any_one: assert property (
        @(posedge clk) $fell(Y) |-> (A || B)
    );

    // A rising to 1 forces Y low in the same cycle.
    check_a_rise_forces_y_low: assert property (
        @(posedge clk) $rose(A) |-> (Y == 1'b0)
    );

    // B rising to 1 forces Y low in the same cycle.
    check_b_rise_forces_y_low: assert property (
        @(posedge clk) $rose(B) |-> (Y == 1'b0)
    );

    // If inputs are stable across a cycle, output is stable.
    check_stable_inputs_imply_stable_output: assert property (
        @(posedge clk) $stable(A) && $stable(B) |-> $stable(Y)
    );

    // If output changes, at least one input changed.
    check_output_change_implies_input_change: assert property (
        @(posedge clk) $changed(Y) |-> ($changed(A) || $changed(B))
    );
endmodule