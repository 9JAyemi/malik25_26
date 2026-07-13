module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic ENCLK,
    input logic TE,
    input logic b1
);

property EnableSynceotid; @(posedge CLK) (EN) |-> ENCLK == TE ; endproperty
assert property (EnableSynceotid);

property ClockGateeotid; @(posedge CLK) (EN) != 1'b1  |-> ENCLK == 0; endproperty
assert property (ClockGateeotid);

endmodule