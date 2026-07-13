module TLATNTSCAX2TS_sva (
    input logic CK,
    input logic E,
    input logic ECK,
    input logic SE,
    input logic clk_osc_19
);

property ClockSynceotid; @(posedge clk_osc_19) (E) &&  (SE) |-> (ECK) ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_osc_19) (E) !=  (SE) &&  (CK) |-> (ECK) !=  (E) ;endproperty
assert property (ClockSynceotid_2);

endmodule