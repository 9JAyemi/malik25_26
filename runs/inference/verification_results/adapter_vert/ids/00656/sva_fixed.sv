module or3_4_custom_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic X,
    input logic clk_osc_16
);

property ORSynceotid; @(posedge clk_osc_16) (A) |-> (X) ;endproperty
assert property (ORSynceotid);

property ORSynceotid_2; @(posedge clk_osc_16) (B) |-> (X) ;endproperty
assert property (ORSynceotid_2);

property ORSynceotid_3; @(posedge clk_osc_16) (C) |-> (X) ;endproperty
assert property (ORSynceotid_3);

property ORSynceotid_4; @(posedge clk_osc_16) (A) && @(posedge clk_osc_16) (B) && @(posedge clk_osc_16) (C) |-> (X) ;endproperty
assert property (ORSynceotid_4);

endmodule