module and2_4_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B
);
    // X equals A & B every cycle.
    check_and_equivalence: assert property (
        @(posedge clk) X == (A & B)
    );

    // If X is HIGH, both A and B are HIGH in the same cycle.
    x_high_implies_inputs_high: assert property (
        @(posedge clk) X |-> (A & B)
    );

    // If any input is LOW, X must be LOW in the same cycle.
    input_low_forces_x_low: assert property (
        @(posedge clk) (!A || !B) |-> (X == 1'b0)
    );

    // X can only rise when both inputs are HIGH.
    x_rise_requires_inputs_high: assert property (
        @(posedge clk) $rose(X) |-> (A & B)
    );

    // X can only fall when at least one input is LOW.
    x_fall_requires_any_input_low: assert property (
        @(posedge clk) $fell(X) |-> (!A || !B)
    );

    // If A and B are unchanged across cycles, X is unchanged.
    stable_inputs_imply_stable_x: assert property (
        @(posedge clk) (($past(A) == A) && ($past(B) == B)) |-> ($past(X) == X)
    );

    // X changes only if at least one input changed across cycles.
    x_change_requires_input_change: assert property (
        @(posedge clk) (X != $past(X)) |-> ((A != $past(A)) || (B != $past(B)))
    );
endmodule