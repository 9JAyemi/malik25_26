module omsp_sync_cell_sva (
    input logic clk,
    input logic data_in,
    input logic data_out,
    input logic data_sync,
    input logic rst,
    input logic b00,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (rst) |-> data_sync == 2'b00 ;endproperty
assert property (ResetSynceotid);

property SyncIneotid; @(posedge clk) (rst) != 1'b1  |-> data_sync == {data_sync[0], data_in} ;endproperty
assert property (SyncIneotid);

property SyncDataeotid; @(posedge clk) (rst) != 1'b1  |-> data_out == data_sync[1] ;endproperty
assert property (SyncDataeotid);

endmodule