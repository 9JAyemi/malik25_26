module crystal_oscillator_interface_assertions #(
    parameter int unsigned osc_freq = 50000000,
    parameter int unsigned clk_div  = 2
) (
    input logic        osc_in,
    input logic        reset,
    input logic        clk_enable,
    input logic        clk_out,
    input logic [31:0] counter
);

    localparam logic [31:0] TERMINAL_COUNT = osc_freq / (2 * clk_div);

    // After reset activity, the sampled state is cleared.
    check_cleared_after_reset: assert property (
        @(posedge osc_in or posedge reset) disable iff (reset)
        ($past(reset) === 1'b1) |-> (counter == 32'd0 && clk_out == 1'b0)
    );

    // Counter increments by one before the terminal count.
    check_counter_increments_below_terminal: assert property (
        @(posedge osc_in or posedge reset) disable iff (reset)
        (counter != TERMINAL_COUNT) |=> (counter == ($past(counter) + 32'd1))
    );

    // Counter wraps to zero at the terminal count.
    check_counter_wraps_at_terminal: assert property (
        @(posedge osc_in or posedge reset) disable iff (reset)
        (counter == TERMINAL_COUNT) |=> (counter == 32'd0)
    );

    // clk_out holds when the counter is below the terminal count.
    check_clk_out_holds_below_terminal: assert property (
        @(posedge osc_in or posedge reset) disable iff (reset)
        (counter != TERMINAL_COUNT) |=> (clk_out == $past(clk_out))
    );

    // clk_out holds at terminal count when clock enable is low.
    check_clk_out_holds_when_disabled: assert property (
        @(posedge osc_in or posedge reset) disable iff (reset)
        (counter == TERMINAL_COUNT && !clk_enable) |=> (clk_out == $past(clk_out))
    );

    // clk_out toggles at terminal count when clock enable is high.
    check_clk_out_toggles_when_enabled: assert property (
        @(posedge osc_in or posedge reset) disable iff (reset)
        (counter == TERMINAL_COUNT && clk_enable) |=> (clk_out == ~$past(clk_out))
    );

endmodule