module my_inverter_sva (
    input  logic clk,
    input  logic Y,
    input  logic in
);
    // Y is always the bitwise inversion of in.
    check_inversion_value: assert property (
        @(posedge clk) (Y === ~in)
    );

    // When in rises, Y falls in the same cycle.
    check_in_rise_y_fall: assert property (
        @(posedge clk) $rose(in) |-> $fell(Y)
    );

    // When in falls, Y rises in the same cycle.
    check_in_fall_y_rise: assert property (
        @(posedge clk) $fell(in) |-> $rose(Y)
    );

    // If in is stable across cycles, Y is stable.
    check_stability_when_input_stable: assert property (
        @(posedge clk) (in === $past(in)) |-> (Y === $past(Y))
    );

    // Any change on Y implies in changed (no internal storage).
    check_y_change_implies_in_change: assert property (
        @(posedge clk) $changed(Y) |-> $changed(in)
    );

    // When in is 0, Y must be 1.
    check_in_low_y_high: assert property (
        @(posedge clk) (in == 1'b0) |-> (Y == 1'b1)
    );

    // When in is 1, Y must be 0.
    check_in_high_y_low: assert property (
        @(posedge clk) (in == 1'b1) |-> (Y == 1'b0)
    );
endmodule