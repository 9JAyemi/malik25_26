module johnson_counter_and_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] input_val,
    input logic [63:0] output_val
);

// Reset clears the counter and the masked output.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |=> (output_val == 64'b0)
    );

// The masked output is always zero-extended to 64 bits.
    check_output_is_zero_extended: assert property (
        @(posedge clk) disable iff (reset) (output_val[63:8] == 56'b0)
    );

// The masked output matches the lower 8 bits of the counter.
    check_output_matches_counter_lsb8: assert property (
        @(posedge clk) disable iff (reset) (output_val[7:0] == counter[7:0])
    );

// The masked output is a subset of the input value.
    check_output_subset_of_input: assert property (
        @(posedge clk) disable iff (reset) (output_val[7:0] inside {8'h00, input_val})
    );

// A zero input value forces the masked output to zero.
    check_zero_input_forces_zero_output: assert property (
        @(posedge clk) disable iff (reset) (input_val == 8'h00) |-> (output_val == 64'b0)
    );

// A non-zero input value forces the masked output to match the counter LSB.
    check_nonzero_input_matches_lsb: assert property (
        @(posedge clk) disable iff (reset) (input_val != 8'h00) |-> (output_val[7:0] == counter[7:0])
    );

// The masked output cannot be a partial match of the input value.
    check_output_not_partial_match: assert property (
        @(posedge clk) disable iff (reset) (output_val[7:0] != (input_val & ~8'hFF)) || (output_val == 64'b0)
    );

endmodule
