module previous_data_sva (
    input logic        clk,
    input logic        rst,
    input logic [31:0] data_in,
    input logic [31:0] data_out
);

    // If reset stays asserted across samples, the output remains zero.
    check_reset_held_clears_output: assert property (
        @(posedge clk)
        !$initstate && rst && $past(rst) |-> (data_out == 32'd0)
    );

    // On the first sampled cycle after reset deasserts, the output is still zero.
    check_post_reset_output_zero: assert property (
        @(posedge clk) disable iff (rst)
        !$initstate && $past(rst) |-> (data_out == 32'd0)
    );

    // With reset low across consecutive cycles, the output matches the prior input.
    check_capture_previous_input: assert property (
        @(posedge clk) disable iff (rst)
        !$initstate && !$past(rst) |-> (data_out == $past(data_in))
    );

endmodule