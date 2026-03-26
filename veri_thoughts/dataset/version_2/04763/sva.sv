module shift_and_check_sva (
    input logic        clk,
    input logic        reset,
    input logic [31:0] input_data,
    input logic [31:0] shifted_data,
    input logic        zero_flag
);

    // A reset cycle clears shifted_data.
    check_reset_clears_shifted_data: assert property (
        @(posedge clk) reset |=> (shifted_data == 32'h00000000)
    );

    // A reset cycle clears zero_flag.
    check_reset_clears_zero_flag: assert property (
        @(posedge clk) reset |=> (zero_flag == 1'b0)
    );

    // shifted_data updates to the prior input_data shifted left by one.
    check_shifted_data_update: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (shifted_data == {$past(input_data[30:0]), 1'b0})
    );

    // A zero input sets zero_flag on the next clock.
    check_zero_flag_set_on_zero_input: assert property (
        @(posedge clk) disable iff (reset)
        (input_data == 32'h00000000) |=> (zero_flag == 1'b1)
    );

    // A nonzero input clears zero_flag on the next clock.
    check_zero_flag_clear_on_nonzero_input: assert property (
        @(posedge clk) disable iff (reset)
        (input_data != 32'h00000000) |=> (zero_flag == 1'b0)
    );

endmodule