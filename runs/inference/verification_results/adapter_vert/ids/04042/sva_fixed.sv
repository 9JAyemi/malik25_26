module clock_gate_sva (
    input logic CLK,
    input logic SE,
    input logic ECK
);

property ClockSynceotid; @(posedge CLK) (SE) |-> (ECK) ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge CLK) (SE) |-> (ECK) ;endproperty
assert property (ClockSynceotid_2);

endmodule