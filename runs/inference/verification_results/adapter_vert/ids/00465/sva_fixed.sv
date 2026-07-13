module up_counter_2bit_sva (
    input logic clk,
    input logic count,
    input logic enable,
    input logic reset,
    input logic b00,
    input logic b1,
    input logic reg_1
);

property ResetSynceotid; @(posedge clk) (reset) |-> count == 2'b00 ;endproperty
assert property (ResetSynceotid);

property EnableSynceotid; @(posedge clk) (reset) != 1'b1 &&  (enable) |-> count == reg_1 ;endproperty
assert property (EnableSynceotid);

property SyncCtrleotid; @(posedge clk) (reset) != 1'b1 &&  !(enable)  |-> count == reg_1 ;endproperty
assert property (SyncCtrleotid);

endmodule