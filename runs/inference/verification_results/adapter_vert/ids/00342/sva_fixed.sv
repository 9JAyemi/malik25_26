module shift_register_sva (
    input logic clk,
    input logic data_in,
    input logic parallel_load,
    input logic parallel_out,
    input logic serial_out,
    input logic shift_dir,
    input logic shift_reg,
    input logic b0
);

property LoadSynceotid; @(posedge clk) (parallel_load) |-> shift_reg == data_in ;endproperty
assert property (LoadSynceotid);

property ShiftIneotid; @(posedge clk) ( !parallel_load ) && (  shift_dir  ) |-> shift_reg == {shift_reg[6:0], 1'b0} ;endproperty
assert property (ShiftIneotid);

property ShiftOuteotid; @(posedge clk) ( !parallel_load ) &&  ( !shift_dir )  |-> shift_reg == {1'b0, shift_reg[7:1]} ;endproperty
assert property (ShiftOuteotid);

property SyncOuteotid; @(posedge clk)  ( serial_out ) == ( shift_reg[0] ) ;endproperty
assert property (SyncOuteotid);

property SyncDataeotid; @(posedge clk)  ( parallel_out ) == ( shift_reg ) ;endproperty
assert property (SyncDataeotid);

endmodule