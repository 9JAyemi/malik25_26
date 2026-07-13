module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic ENCLK,
    input logic RST,
    input logic TE,
    input logic b1
);

property ResetSynceotid; @(posedge CLK) (RST) |-> ENCLK == 0 ;endproperty
assert property (ResetSynceotid);

property EnableSynceotid; @(posedge CLK) (RST) != 1'b1 &&  (TE) |-> ENCLK == EN ;endproperty
assert property (EnableSynceotid);

endmodule