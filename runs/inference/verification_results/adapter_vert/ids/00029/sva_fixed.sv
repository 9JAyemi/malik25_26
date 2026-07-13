module binary_counter_sva (
    input logic clk,
    input logic enable,
    input logic q,
    input logic reset,
    input logic b0000,
    input logic reg_1
);

property ResetSynceotid; @(posedge clk) (reset) |-> q == 4'b0000 ;endproperty
assert property (ResetSynceotid);

property EnableSynceotid; @(posedge clk) (enable) && !(reset) |-> q == reg_1 ;endproperty
assert property (EnableSynceotid);

endmodule