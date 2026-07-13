module clock_100kHz_sva (
    input logic        clk,
    input logic        rst_n,
    input logic        out_100kHz,
    input logic [15:0] counter
);

    // Reset drives both registers low.
    check_reset_clears_registers: assert property (
        @(posedge clk)
        !rst_n |-> ((out_100kHz == 1'b0) && (counter == 16'd0))
    );

    // Counter never exceeds the terminal count.
    check_counter_range: assert property (
        @(posedge clk) disable iff (!rst_n)
        (counter <= 16'd499)
    );

    // Counter increments by one when not at terminal count.
    check_counter_increments_below_terminal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (counter != 16'd499) |=> (counter == ($past(counter) + 16'd1))
    );

    // Output holds its value when not at terminal count.
    check_output_holds_below_terminal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (counter != 16'd499) |=> (out_100kHz == $past(out_100kHz))
    );

    // Counter wraps to zero at terminal count.
    check_counter_wraps_at_terminal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (counter == 16'd499) |=> (counter == 16'd0)
    );

    // Output toggles when terminal count is reached.
    check_output_toggles_at_terminal: assert property (
        @(posedge clk) disable iff (!rst_n)
        (counter == 16'd499) |=> (out_100kHz == !$past(out_100kHz))
    );

endmodule