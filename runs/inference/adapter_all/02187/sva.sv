module data_storage_sva (
    input logic        clk,
    input logic        reset,
    input logic [31:0] in_data,
    input logic        in_valid,
    input logic [31:0] out_data,
    input logic        out_valid
);

    // Reset clears the stored data and deasserts the output valid flag.
    check_reset_clears_outputs: assert property (
        @(posedge clk) reset |=> (out_data == 32'h0000_0000 && out_valid == 1'b0)
    );

    // With valid input, the output reflects the prior input data and valid flag.
    check_valid_input_updates_output: assert property (
        @(posedge clk) disable iff (reset)
        in_valid |=> (out_data == $past(in_data) && out_valid == 1'b1)
    );

    // Without valid input, the output valid flag is deasserted on the next cycle.
    check_no_valid_input_deasserts_valid: assert property (
        @(posedge clk) disable iff (reset)
        !in_valid |=> (out_valid == 1'b0)
    );

    // The output data always matches the stored data from the previous cycle.
    check_output_data_matches_previous_storage: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (out_data == $past(out_data))
    );

    // A high output valid flag must come from a prior valid input.
    check_valid_output_requires_prior_valid_input: assert property (
        @(posedge clk) disable iff (reset)
        out_valid |-> $past(in_valid)
    );

endmodule