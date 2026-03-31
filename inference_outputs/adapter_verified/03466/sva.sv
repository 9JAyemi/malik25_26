module sync_signal_sva (
    input logic clk,
    input logic in,
    input logic out,
    input logic falling,
    input logic rising
);

// out is the registered input value from two cycles ago.
    check_out_registered_two_cycle_delay: assert property (
        @(posedge clk) 1'b1 |=> ##2 (out == $past(in, 2))
    );

// falling is asserted exactly when the input was low two cycles ago and high one cycle ago.
    check_falling_definition: assert property (
        @(posedge clk) 1'b1 |=> ##2 (falling == ($past(in, 2) == 1'b0) && ($past(in, 1) == 1'b1))
    );

// rising is asserted exactly when the input was high two cycles ago and low one cycle ago.
    check_rising_definition: assert property (
        @(posedge clk) 1'b1 |=> ##2 (rising == ($past(in, 2) == 1'b1) && ($past(in, 1) == 1'b0))
    );

// falling and rising are never asserted together.
    check_edge_mutex: assert property (
        @(posedge clk) 1'b1 |=> ##2 !(falling && rising)
    );

// Exactly one of out, falling, or rising is asserted each cycle.
    check_onehot_out_falling_rising: assert property (
        @(posedge clk) 1'b1 |=> ##2 $onehot({out, falling, rising})
    );

endmodule
