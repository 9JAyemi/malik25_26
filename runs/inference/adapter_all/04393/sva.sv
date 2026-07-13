module omsp_sync_cell_sva (
    input logic data_out,
    input logic clk,
    input logic data_in,
    input logic rst,
    input logic [1:0] data_sync
);

    // Reset forces the internal register low.
    check_reset_clears_data_sync: assert property (
        @(posedge clk) rst |-> (data_sync == 2'b00)
    );

    // Reset forces the output low.
    check_reset_clears_data_out: assert property (
        @(posedge clk) rst |-> (data_out == 1'b0)
    );

    // The output reflects the previous cycle's reset state.
    check_reset_propagates_to_output: assert property (
        @(posedge clk) $past(rst) |-> (data_out == 1'b0)
    );

    // The upper register bit shifts in the previous lower bit.
    check_data_sync_shifts_upper: assert property (
        @(posedge clk) disable iff (rst) data_sync[1] == $past(data_sync[0])
    );

    // The lower register bit captures the previous input bit.
    check_data_sync_captures_lower: assert property (
        @(posedge clk) disable iff (rst) data_sync[0] == $past(data_in)
    );

    // The output is the previous cycle's shifted register value.
    check_data_out_shifts_from_previous: assert property (
        @(posedge clk) disable iff (rst) data_out == $past(data_sync[0])
    );

    // The output is the previous cycle's captured input bit.
    check_data_out_captures_previous_input: assert property (
        @(posedge clk) disable iff (rst) data_out == $past(data_in)
    );

endmodule