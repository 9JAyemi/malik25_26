module omsp_sync_cell_sva (
    input logic clk,
    input logic rst,
    input logic data_in,
    input logic data_out,
    input logic [1:0] data_sync
);

    // Reset clears the internal state and forces the output low.
    check_reset_clears_state: assert property (
        @(posedge clk) rst |-> ((data_sync == 2'b00) && (data_out == 1'b0))
    );

    // The first clock after reset release still sees the cleared state.
    check_post_reset_state: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> ((data_sync == 2'b00) && (data_out == 1'b0))
    );

    // The output is always the previous cycle's shifted state bit.
    check_output_matches_previous_state: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> (data_out == $past(data_sync[0]))
    );

    // The upper state bit captures the previous cycle's shifted input bit.
    check_upper_state_captures_input: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> (data_sync[1] == $past(data_in))
    );

    // The lower state bit captures the previous cycle's upper state bit.
    check_lower_state_captures_upper: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> (data_sync[0] == $past(data_sync[1]))
    );

    // The output is the delayed input bit from two cycles earlier.
    check_output_is_two_cycle_input_delay: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |-> (data_out == $past(data_in, 2))
    );

endmodule