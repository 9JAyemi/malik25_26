module digital_circuit_sva (
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic Y,
    input logic and0_out,
    input logic b,
    input logic nor0_out_Y,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (b) == ( !B1_N ) ;endproperty
assert property (ClockSynceotid);

property SyncIneotid; @(posedge clk_in_1) (and0_out) == (  A1  &&  A2  ) ;endproperty
assert property (SyncIneotid);

property SyncCheckeotid; @(posedge clk_in_1) (nor0_out_Y) == (  !(b)  &&  !(and0_out)  ) ;endproperty
assert property (SyncCheckeotid);

property SyncSafeeotid; @(posedge clk_in_1) (Y) == (  !(b)  &&  !(and0_out)  ) ;endproperty
assert property (SyncSafeeotid);

endmodule