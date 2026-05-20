module counter_4bit_sva (
    input logic clk,
    input logic count,
    input logic enable,
    input logic reset,
    input logic b0000,
    input logic b1,
    input logic reg_15,
    input logic reg_16
);

property ResetSynceotid; @(posedge clk) (reset) |-> count == 4'b0000 ;endproperty
assert property (ResetSynceotid);

property EnableSynceotid; @(posedge clk) (reset) != 1'b1 &&  (enable) |-> count == reg_15 ;endproperty
assert property (EnableSynceotid);

property SyncCtrleotid; @(posedge clk) (reset) != 1'b1 &&  !(enable)  |-> count == reg_16 ;endproperty
assert property (SyncCtrleotid);

endmodule