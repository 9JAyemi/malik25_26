module johnson_counter_and_sva (
    input logic        clk,
    input logic        reset,
    input logic [7:0]  input_val,
    input logic [63:0] output_val,
    input logic [63:0] counter
);

    // Reset clears the counter on the next clock.
    check_reset_clears_counter: assert property (
        @(posedge clk) reset |=> (counter == 64'b0)
    );

    // Reset clears the output on the next clock.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |=> (output_val == 64'b0)
    );

    // The counter follows the Johnson shift register update.
    check_counter_update: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (counter == {$past(counter[62:0]), $past(counter[63] ^ counter[0])})
    );

    // The output is the counter masked by the repeated input value.
    check_output_masking: assert property (
        @(posedge clk) disable iff (reset)
        (output_val == (counter & {64{input_val}}))
    );

    // The output bits are either 0 or the corresponding input bit.
    check_output_subset_of_input: assert property (
        @(posedge clk) disable iff (reset)
        ((output_val & ~{64{input_val}}) == 64'b0)
    );

    // The output bits are either 0 or the corresponding counter bit.
    check_output_subset_of_counter: assert property (
        @(posedge clk) disable iff (reset)
        ((output_val & ~counter) == 64'b0)
    );

    // A zero input forces the output low.
    check_zero_input_forces_zero_output: assert property (
        @(posedge clk) disable iff (reset)
        (input_val == 8'h00) |-> (output_val == 64'b0)
    );

    // A zero counter forces the output low.
    check_zero_counter_forces_zero_output: assert property (
        @(posedge clk) disable iff (reset)
        (counter == 64'b0) |-> (output_val == 64'b0)
    );

    // All ones in the input pass through the counter bits.
    check_all_ones_input_passes_counter: assert property (
        @(posedge clk) disable iff (reset)
        (input_val == 8'hFF) |-> (output_val == counter)
    );

    // All ones in the counter pass through the input bits.
    check_all_ones_counter_passes_input: assert property (
        @(posedge clk) disable iff (reset)
        (counter == 64'hFFFF_FFFF_FFFF_FFFF) |-> (output_val == {64{input_val}})
    );

endmodule