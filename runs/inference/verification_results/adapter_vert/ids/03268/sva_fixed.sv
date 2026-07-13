module binary_counter_sva (
    input logic clk,
    input logic count,
    input logic enable,
    input logic reset,
    input logic b0,
    input logic b1,
    input logic reg_14
);

property ResetSynceotid; @(posedge clk) (reset) |-> count == 4'b0 ;endproperty
assert property (ResetSynceotid);

property EnableSynceotid; @(posedge clk) (reset) != 1'b1 &&  (enable)  |-> count == reg_14 ;endproperty
assert property (EnableSynceotid);

endmodule