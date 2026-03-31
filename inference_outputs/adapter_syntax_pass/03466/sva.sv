module sync_signal_sva (
    input logic clk,
    input logic in,
    input logic out,
    input logic falling,
    input logic rising
);

    // out is the registered input bit from the previous clock.
    check_out_tracks_previous_input: assert property (
        @(posedge clk) 1'b1 |=> (out == $past(in))
    );

    // falling is high only when the previous two stages were 10.
    check_falling_decode: assert property (
        @(posedge clk) 1'b1 |=> (falling == ($past(shiftreg[2]) & ~$past(shiftreg[1])))
    );

    // rising is high only when the previous two stages were 01.
    check_rising_decode: assert property (
        @(posedge clk) 1'b1 |=> (rising == (~$past(shiftreg[2]) & $past(shiftreg[1])))
    );

    // falling and rising are never asserted together.
    check_falling_rising_mutex: assert property (
        @(posedge clk) 1'b1 |=> !(falling && rising)
    );

    // out is the OR of the two edge outputs.
    check_out_is_edge_or: assert property (
        @(posedge clk) 1'b1 |=> (out == (falling | rising))
    );

    // A high out must come from a previous rising edge.
    check_out_implies_previous_rise: assert property (
        @(posedge clk) 1'b1 |=> (out == 1'b0 || $past(rising))
    );

    // A low out must come from a previous falling edge.
    check_out_low_implies_previous_fall: assert property (
        @(posedge clk) 1'b1 |=> (out == 1'b1 || $past(falling))
    );

endmodule