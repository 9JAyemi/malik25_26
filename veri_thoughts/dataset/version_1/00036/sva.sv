module clock_generator_sva (
    input logic clk_in,
    input logic clk_out,
    input logic [23:0] counter
);

localparam logic [23:0] TERMINAL_COUNT = 24'd4_999_999;

// Counter wraps to zero after the terminal count.
check_counter_wrap: assert property (
    @(posedge clk_in) disable iff (1'b0)
    (counter == TERMINAL_COUNT) |=> (counter == 24'd0)
);

// clk_out toggles when the terminal count is reached.
check_clk_out_toggle_on_wrap: assert property (
    @(posedge clk_in) disable iff (1'b0)
    (counter == TERMINAL_COUNT) |=> (clk_out != $past(clk_out))
);

// Counter increments by one on all non-terminal cycles.
check_counter_increment_otherwise: assert property (
    @(posedge clk_in) disable iff (1'b0)
    (counter != TERMINAL_COUNT) |=> (counter == ($past(counter) + 24'd1))
);

// clk_out holds its value on all non-terminal cycles.
check_clk_out_hold_otherwise: assert property (
    @(posedge clk_in) disable iff (1'b0)
    (counter != TERMINAL_COUNT) |=> (clk_out == $past(clk_out))
);

endmodule