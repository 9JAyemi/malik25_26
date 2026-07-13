module top_module_assertions (
    input logic       clk,
    input logic       reset,
    input logic [7:0] d,
    input logic [3:0] counter_out,
    input logic [7:0] max_out
);

    // A reset cycle drives the counter output to zero on the next observed cycle.
    check_reset_counter_zero: assert property (
        @(posedge clk) reset |=> (counter_out == 4'h0)
    );

    // A reset cycle drives the max output to the reset register value.
    check_reset_max_constant: assert property (
        @(posedge clk) reset |=> (max_out == 8'h34)
    );

    // Outside reset, the counter increments by one with wraparound.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && !$past(reset) |-> (counter_out == (($past(counter_out) == 4'hf) ? 4'h0 : ($past(counter_out) + 4'h1)))
    );

    // The max output is never smaller than the zero-extended counter.
    check_max_not_below_counter: assert property (
        @(posedge clk) disable iff (reset)
        (max_out >= {4'b0, counter_out})
    );

    // After a non-reset cycle, the max output is never smaller than the loaded data.
    check_max_not_below_prev_d: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && !$past(reset) |-> (max_out >= $past(d))
    );

    // After a non-reset cycle, max_out matches the max of the loaded data and counter.
    check_max_matches_function: assert property (
        @(posedge clk) disable iff (reset)
        !$initstate && !$past(reset) |-> (max_out == (($past(d) > {4'b0, counter_out}) ? $past(d) : {4'b0, counter_out}))
    );

endmodule