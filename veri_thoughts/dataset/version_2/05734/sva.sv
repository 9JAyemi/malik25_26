module top_module_sva(
    input logic clk,
    input logic reset,
    input logic up_down,
    input logic [3:0] add_value,
    input logic [3:0] out,
    input logic [3:0] counter_out,
    input logic [3:0] adder_out
);

    // Top-level output must mirror the adder output.
    check_output_matches_adder: assert property (
        @(posedge clk) disable iff (reset) out == adder_out
    );

    // Adder output must equal counter_out plus add_value.
    check_adder_function: assert property (
        @(posedge clk) disable iff (reset) adder_out == (counter_out + add_value)
    );

    // After a reset cycle, the counter output must be zero.
    check_counter_clears_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(reset)) |-> (counter_out == 4'b0000)
    );

    // After a reset cycle, the final output must equal add_value.
    check_output_after_reset: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(reset)) |-> (out == add_value)
    );

    // When counting up, the counter increments by one.
    check_counter_counts_up: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset) && $past(up_down)) |-> (counter_out == ($past(counter_out) + 4'd1))
    );

    // When counting down, the counter decrements by one.
    check_counter_counts_down: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && !$past(reset) && !$past(up_down)) |-> (counter_out == ($past(counter_out) - 4'd1))
    );

endmodule