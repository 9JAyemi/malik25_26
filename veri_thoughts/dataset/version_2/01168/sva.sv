module kernel_clock_0_bit_pipe_sva (
    input logic clk1,
    input logic clk2,
    input logic data_in,
    input logic reset_clk1_n,
    input logic reset_clk2_n,
    input logic data_out,
    // Internal RTL signal exposed via bind
    input logic data_in_d1
);

    ///// clk1 domain reset behavior for data_in_d1 /////
    // If clk1 reset was LOW at the previous clk1 edge, data_in_d1 must be 0 now.
    check_clk1_prev_reset_low_zero_now: assert property (
        @(posedge clk1) !$past(reset_clk1_n) |-> (data_in_d1 == 1'b0)
    );

    // If clk1 reset is LOW at this clk1 edge, data_in_d1 must be 0 at the next clk1 edge.
    check_clk1_reset_low_next_zero: assert property (
        @(posedge clk1) !reset_clk1_n |-> ##1 (data_in_d1 == 1'b0)
    );

    // If clk1 reset is LOW in two consecutive clk1 edges, data_in_d1 must be 0 now.
    check_clk1_consecutive_reset_low_zero: assert property (
        @(posedge clk1) (!reset_clk1_n && !$past(reset_clk1_n)) |-> (data_in_d1 == 1'b0)
    );

    // On clk1 reset deassertion, data_in_d1 is 0 at that clk1 sample.
    check_clk1_reset_release_zero_sample: assert property (
        @(posedge clk1) disable iff (!reset_clk1_n) $rose(reset_clk1_n) |-> (data_in_d1 == 1'b0)
    );

    ///// clk2 domain reset behavior for data_out /////
    // If clk2 reset was LOW at the previous clk2 edge, data_out must be 0 now.
    check_clk2_prev_reset_low_zero_now: assert property (
        @(posedge clk2) !$past(reset_clk2_n) |-> (data_out == 1'b0)
    );

    // If clk2 reset is LOW at this clk2 edge, data_out must be 0 at the next clk2 edge.
    check_clk2_reset_low_next_zero: assert property (
        @(posedge clk2) !reset_clk2_n |-> ##1 (data_out == 1'b0)
    );

    // If clk2 reset is LOW in two consecutive clk2 edges, data_out must be 0 now.
    check_clk2_consecutive_reset_low_zero: assert property (
        @(posedge clk2) (!reset_clk2_n && !$past(reset_clk2_n)) |-> (data_out == 1'b0)
    );

    // On clk2 reset deassertion, data_out is 0 at that clk2 sample.
    check_clk2_reset_release_zero_sample: assert property (
        @(posedge clk2) disable iff (!reset_clk2_n) $rose(reset_clk2_n) |-> (data_out == 1'b0)
    );

endmodule