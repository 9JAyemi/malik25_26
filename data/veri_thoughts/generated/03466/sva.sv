module sync_signal_sva (
    input logic clk,
    input logic in,
    input logic out,
    input logic falling,
    input logic rising
);

    // The initial clear sets all observed outputs low on the first clock.
    check_initial_outputs_low: assert property (
        @(posedge clk) $initstate |-> (!out && !falling && !rising)
    );

    // A sampled high input appears on out two clocks later.
    check_out_high_after_two_cycles: assert property (
        @(posedge clk) in |-> ##2 out
    );

    // A sampled low input appears on out two clocks later.
    check_out_low_after_two_cycles: assert property (
        @(posedge clk) !in |-> ##2 !out
    );

    // An input rising edge produces a rising pulse two clocks later.
    check_rising_after_input_rise: assert property (
        @(posedge clk) !$initstate && $rose(in) |-> ##2 rising
    );

    // An input falling edge produces a falling pulse two clocks later.
    check_falling_after_input_fall: assert property (
        @(posedge clk) !$initstate && $fell(in) |-> ##2 falling
    );

    // Rising is asserted exactly when out transitions from 0 to 1.
    check_rising_matches_out_rise: assert property (
        @(posedge clk) !$initstate |-> (rising == (!$past(out) && out))
    );

    // Falling is asserted exactly when out transitions from 1 to 0.
    check_falling_matches_out_fall: assert property (
        @(posedge clk) !$initstate |-> (falling == ($past(out) && !out))
    );

    // Rising and falling can never be asserted together.
    check_edge_flags_mutex: assert property (
        @(posedge clk) !(rising && falling)
    );

    // A rising pulse implies out is high in that cycle.
    check_rising_implies_out_high: assert property (
        @(posedge clk) rising |-> out
    );

    // A falling pulse implies out is low in that cycle.
    check_falling_implies_out_low: assert property (
        @(posedge clk) falling |-> !out
    );

endmodule