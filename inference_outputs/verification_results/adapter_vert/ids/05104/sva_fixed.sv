module counter_sva (
    input logic clk,
    input logic count,
    input logic enable,
    input logic reset,
    input logic b0,
    input logic reg_16
);

property ResetSynceotid; @(posedge clk) (reset) |-> count == 2'b0 ;endproperty
assert property (ResetSynceotid);

property EnableSynceotid; @(posedge clk) (enable) && !(reset) |->  count == reg_16 ;endproperty
assert property (EnableSynceotid);

endmodule