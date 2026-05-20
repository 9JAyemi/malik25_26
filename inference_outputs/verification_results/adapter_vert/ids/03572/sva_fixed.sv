module ClockGating_sva (
    input logic CLK,
    input logic EN,
    input logic ENCLK,
    input logic RESET,
    input logic TE
);

property ResetSynceotid; @(posedge CLK) (RESET) |-> ENCLK == 0 ;endproperty
assert property (ResetSynceotid);

property EnableSynceotid; @(posedge CLK) (EN) && !(TE)  |-> ENCLK == ~CLK ;endproperty
assert property (EnableSynceotid);

property ClockSynceotid; @(posedge CLK) (EN) && (TE)  |-> ENCLK == 0 ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge CLK) ! (EN)  |-> ENCLK == 0 ;endproperty
assert property (ClockSynceotid_2);

endmodule