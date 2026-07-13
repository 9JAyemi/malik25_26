module omsp_sync_cell_sva (
    input logic clk,
    input logic rst,
    input logic data_in,
    output logic data_out
);
    // Sequential logic: data_sync register is updated on the rising edge of clk or on reset
    // Reset behavior: data_sync is reset to 2'b00 on the rising edge of rst
    reset_behavior: assert property (
        @(posedge clk) disable iff (!rst) (rst |-> data_sync == 2'b00)
    );

    // Sequential logic: data_sync register shifts left and data_in is loaded on the rising edge of clk
    // Data synchronization behavior: data_out is the second bit of data_sync
    data_sync_behavior: assert property (
        @(posedge clk) disable iff (!rst) (data_out == data_sync[1])
    );

    // Sequential logic: data_sync register shifts left and data_in is loaded on the rising edge of clk
    // Data synchronization behavior: data_sync[0] is the first bit of data_sync
    data_sync_shift: assert property (
        @(posedge clk) disable iff (!rst) (data_sync[0] == data_sync[1])
    );
endmodule