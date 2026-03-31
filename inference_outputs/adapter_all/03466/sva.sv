module sync_signal_sva (
    input logic clk,
    input logic in,
    input logic out,
    input logic falling,
    input logic rising
);

    // out is the registered copy of the input from two clocks earlier.
    check_out_two_cycle_delay: assert property (
        @(posedge clk) 1'b1 |-> ##2 (out == $past(in, 2))
    );

    // falling is high only when the two-cycle delayed input was low and is high now.
    check_falling_definition: assert property (
        @(posedge clk) 1'b1 |-> ##2 (falling == ($past(in, 2) & ~in))
    );

    // rising is high only when the two-cycle delayed input was high and is low now.
    check_rising_definition: assert property (
        @(posedge clk) 1'b1 |-> ##2 (rising == (~$past(in, 2) & in))
    );

    // falling and rising cannot be high at the same time.
    check_falling_rising_mutex: assert property (
        @(posedge clk) 1'b1 |-> ##2 !(falling & rising)
    );

    // out, falling, and rising are all low on the first clock after reset.
    check_reset_initial_state: assert property (
        @(posedge clk) $initstate |-> (out == 1'b0 && falling == 1'b0 && rising == 1'b0)
    );

    // out, falling, and rising are all low on the second clock after reset.
    check_reset_second_cycle_state: assert property (
        @(posedge clk) $past($initstate) |-> (out == 1'b0 && falling == 1'b0 && rising == 1'b0)
    );

endmodule