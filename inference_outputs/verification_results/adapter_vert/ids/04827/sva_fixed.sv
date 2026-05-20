module mux4to1_sva (
    input logic in0,
    input logic in2,
    input logic in3,
    input logic out,
    input logic sel0,
    input logic sel1,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (sel0) |-> (out) == (in0) ; endproperty
assert property (ClockSynceotid);

property SyncIneotid; @(posedge clk_in_1) (sel0) &&  (  !(sel0)  &&  (sel1)  ) |-> (out) == (in2) ; endproperty
assert property (SyncIneotid);

property SyncOuteotid; @(posedge clk_in_1) (  !(sel0)  &&  !(sel1)  ) |-> (out) == (in3) ; endproperty
assert property (SyncOuteotid);

endmodule