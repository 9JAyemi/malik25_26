module top_module_assertions (
    input logic        clk,
    input logic        reset,
    input logic [7:0]  out_hi,
    input logic [7:0]  out_lo,
    input logic [15:0] final_out,
    input logic [3:0]  counter,
    input logic [15:0] input_num
);

    // Splitter drives the upper byte from input_num.
    check_split_hi_mapping: assert property (
        @(posedge clk) disable iff (reset)
        out_hi == input_num[15:8]
    );

    // Splitter drives the lower byte from input_num.
    check_split_lo_mapping: assert property (
        @(posedge clk) disable iff (reset)
        out_lo == input_num[7:0]
    );

    // Combiner reconstructs final_out from the two output bytes.
    check_combiner_concat: assert property (
        @(posedge clk) disable iff (reset)
        final_out == {out_hi, out_lo}
    );

    // The split/combine path preserves input_num.
    check_final_matches_input_num: assert property (
        @(posedge clk) disable iff (reset)
        final_out == input_num
    );

    // Counter increments by one on consecutive non-reset cycles.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !$past(reset) |-> (counter == $past(counter) + 4'd1)
    );

    // input_num increments by one on consecutive non-reset cycles.
    check_input_num_increments: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !$past(reset) |-> (input_num == $past(input_num) + 16'd1)
    );

    // final_out increments by one on consecutive non-reset cycles.
    check_final_out_increments: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !$past(reset) |-> (final_out == $past(final_out) + 16'd1)
    );

    // A reset cycle clears counter by the following clock.
    check_counter_clears_after_reset: assert property (
        @(posedge clk)
        reset |=> (counter == 4'd0)
    );

    // A reset cycle clears input_num by the following clock.
    check_input_num_clears_after_reset: assert property (
        @(posedge clk)
        reset |=> (input_num == 16'd0)
    );

    // A reset cycle clears all outputs by the following clock.
    check_outputs_clear_after_reset: assert property (
        @(posedge clk)
        reset |=> (out_hi == 8'd0 && out_lo == 8'd0 && final_out == 16'd0)
    );

endmodule