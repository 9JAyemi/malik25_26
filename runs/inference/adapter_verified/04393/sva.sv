module omsp_sync_cell_sva (
    input logic data_out,
    input logic clk,
    input logic data_in,
    input logic rst
);

// Reset drives data_out low on the next clock.
    check_reset_clears_output: assert property (
        @(posedge clk) rst |=> (data_out == 1'b0)
    );

// data_out is the previous cycle's data_in.
    check_output_follows_input: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (data_out == $past(data_in))
    );

// A high input is captured as high on the next clock.
    check_high_input_captured: assert property (
        @(posedge clk) disable iff (rst) data_in |=> (data_out == 1'b1)
    );

// A low input is captured as low on the next clock.
    check_low_input_captured: assert property (
        @(posedge clk) disable iff (rst) !data_in |=> (data_out == 1'b0)
    );

endmodule
