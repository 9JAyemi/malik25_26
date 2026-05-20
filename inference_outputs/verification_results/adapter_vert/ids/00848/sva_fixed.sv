module vfabric_bypass_reg_sva (
    input logic clock,
    input logic i_datain_valid,
    input logic i_dataout_stall,
    input logic i_register_settings,
    input logic i_settings,
    input logic o_datain_stall,
    input logic o_dataout,
    input logic o_dataout_valid
);

property SyncIneotid; @(posedge clock) (i_settings) |-> (o_dataout == i_register_settings) ;endproperty
assert property (SyncIneotid);

property ValidDataeotid; @(posedge clock) (i_settings) |-> (o_dataout_valid == i_datain_valid) ;endproperty
assert property (ValidDataeotid);

property SyncCheckeotid; @(posedge clock) (i_settings) |-> (o_datain_stall == i_dataout_stall) ;endproperty
assert property (SyncCheckeotid);

endmodule