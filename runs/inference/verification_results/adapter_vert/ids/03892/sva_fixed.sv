module bin_counter_sva (
    input logic clk,
    input logic count,
    input logic enable,
    input logic reset,
    input logic b0,
    input logic reg_1
);

property ResetSynceotid; @(posedge clk) (reset) |-> count == 4'b0 ;endproperty
assert property (ResetSynceotid);

property EnableSynceotid; @(posedge clk) (enable) && !(reset) |-> count == reg_1 ;endproperty
assert property (EnableSynceotid);

endmodule