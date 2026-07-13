module counter_sva (
    input logic CLK,
    input logic count,
    input logic enable,
    input logic reset,
    input logic b0,
    input logic b1,
    input logic reg_15
);

property ResetSynceotid; @(posedge CLK) (reset) |-> count == 4'b0 ;endproperty
assert property (ResetSynceotid);

property EnableSynceotid; @(posedge CLK) (reset) != 1'b1 &&  (enable) |-> count == reg_15 ;endproperty
assert property (EnableSynceotid);

endmodule