module ResetInverter_sva (
    input logic clk,
    input logic RESET_IN,
    input logic RESET_OUT
);

    // Output is always the logical inverse of the input.
    check_output_is_inverse: assert property (
        @(posedge clk) disable iff (1'b0)
        (RESET_OUT === !RESET_IN)
    );

    // Low input drives a high output.
    check_low_input_drives_high_output: assert property (
        @(posedge clk) disable iff (1'b0)
        (RESET_IN === 1'b0) |-> (RESET_OUT === 1'b1)
    );

    // High input drives a low output.
    check_high_input_drives_low_output: assert property (
        @(posedge clk) disable iff (1'b0)
        (RESET_IN === 1'b1) |-> (RESET_OUT === 1'b0)
    );

    // High output implies the input is low.
    check_high_output_means_low_input: assert property (
        @(posedge clk) disable iff (1'b0)
        (RESET_OUT === 1'b1) |-> (RESET_IN === 1'b0)
    );

    // Low output implies the input is high.
    check_low_output_means_high_input: assert property (
        @(posedge clk) disable iff (1'b0)
        (RESET_OUT === 1'b0) |-> (RESET_IN === 1'b1)
    );

endmodule