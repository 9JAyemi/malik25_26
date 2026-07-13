module johnson_counter_and_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] input_val,
    input logic [63:0] output_val,
    input logic [63:0] counter
);
    // On reset, counter must be all zeros on the next cycle.
    check_reset_clears_counter_next: assert property (
        @(posedge clk) reset |=> (counter == 64'b0)
    );

    // On reset, output must be all zeros on the next cycle.
    check_reset_clears_output_next: assert property (
        @(posedge clk) reset |=> (output_val == 64'b0)
    );

    // When not in reset, counter updates with shift and XOR of MSB and LSB from previous cycle.
    check_counter_update_rule: assert property (
        @(posedge clk) disable iff (reset)
            counter == { $past(counter[62:0]), $past(counter[63]) ^ $past(counter[0]) }
    );

    // Zero counter state remains zero on the next cycle when not in reset.
    check_zero_state_absorbing: assert property (
        @(posedge clk) disable iff (reset)
            (counter == 64'b0) |=> (counter == 64'b0)
    );

    // Output equals counter AND the 64-bit replicated input mask.
    check_output_matches_and_mask: assert property (
        @(posedge clk) disable iff (reset)
            output_val == (counter & {8{input_val}})
    );

    // Output bits can only be 1 where the replicated input mask bits are 1.
    check_output_mask_subset: assert property (
        @(posedge clk) disable iff (reset)
            (output_val & ~{8{input_val}}) == 64'b0
    );

    // If the input mask is all zeros, the output must be zero.
    check_output_zero_when_input_zero: assert property (
        @(posedge clk) disable iff (reset)
            (input_val == 8'h00) |-> (output_val == 64'b0)
    );

    // If the input mask is all ones, the output equals the counter.
    check_output_equals_counter_when_mask_all_ones: assert property (
        @(posedge clk) disable iff (reset)
            (input_val == 8'hFF) |-> (output_val == counter)
    );
endmodule