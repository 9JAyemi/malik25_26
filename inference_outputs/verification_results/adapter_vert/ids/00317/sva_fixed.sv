module TLATNTSCAX2TS_sva (
    input logic CK,
    input logic CLK,
    input logic E,
    input logic ECK,
    input logic ENCLK,
    input logic SE
);

property ClockSynceotid; @(posedge CLK) (SE) |-> (ECK) ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge CLK) (SE) |-> (E) ;endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge CLK) (SE) |-> (SE) ;endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge CLK) (SE) |-> (CK) ;endproperty
assert property (ClockSynceotid_4);

property ClockSynceotid_5; @(posedge CLK) (SE) |-> (ENCLK) ;endproperty
assert property (ClockSynceotid_5);

endmodule