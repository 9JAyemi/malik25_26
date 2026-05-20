module and_module_sva (
    input logic i_bus1,
    input logic i_bus2,
    input logic o_bus,
    input logic clk_in_15
);

property SyncIneotid; @(posedge clk_in_15) (i_bus1) && (i_bus2) |-> (o_bus) ;endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(posedge clk_in_15) (i_bus1) && !(i_bus2) |-> !(o_bus) ;endproperty
assert property (SyncIneotid_2);

property SyncIneotid_3; @(posedge clk_in_15) !(i_bus1) && (i_bus2) |-> !(o_bus) ;endproperty
assert property (SyncIneotid_3);

property SyncIneotid_4; @(posedge clk_in_15) !(i_bus1) && !(i_bus2) |-> !(o_bus) ;endproperty
assert property (SyncIneotid_4);

endmodule