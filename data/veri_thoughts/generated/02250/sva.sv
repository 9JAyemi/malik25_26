module top_module_sva (
    input logic clk,
    input logic reset,            // Synchronous active-high reset
    input logic [7:0] d,
    input logic [3:0] counter_out,
    input logic [7:0] register_out,
    input logic [7:0] final_out
);
    // During reset, outputs reflect reset values and their sum.
    check_reset_values: assert property (
        @(posedge clk) reset |-> (counter_out == 4'd0) && (register_out == 8'h34) && (final_out == 8'h34)
    );

    // final_out equals the sum of register_out and counter_out each cycle.
    check_final_sum_comb: assert property (
        @(posedge clk) final_out == (register_out + counter_out)
    );

    // Counter increments by 1 each cycle when not in or coming out of reset.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (counter_out == ($past(counter_out) + 4'd1))
    );

    // Counter wraps from 15 to 0 on the next non-reset cycle.
    check_counter_wrap: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && ($past(counter_out) == 4'hF)) |-> (counter_out == 4'h0)
    );

    // On the first non-reset cycle after reset, counter advances from its reset value.
    check_counter_after_reset_release: assert property (
        @(posedge clk) disable iff (reset) ($past(reset) && !reset) |-> (counter_out == ($past(counter_out) + 4'd1))
    );

    // Register captures input d on the next cycle when not in or coming out of reset.
    check_register_tracks_d: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (register_out == $past(d))
    );

    // Given sequential updates, final_out equals past d plus incremented past counter_out.
    check_final_from_past: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (final_out == ($past(d) + ($past(counter_out) + 4'd1)))
    );
endmodule