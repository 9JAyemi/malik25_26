module counter_4bit_sva (
    input logic clk,
    input logic count_reg,
    input logic enable,
    input logic reset,
    input logic b0,
    input logic b1,
    input logic reg_15
);

property ResetSynceotid; @(posedge clk) (reset) |-> count_reg == 4'b0 ;endproperty
assert property (ResetSynceotid);

property EnableSynceotid; @(posedge clk) (reset) != 1'b1 &&  (enable) |-> count_reg == reg_15 ;endproperty
assert property (EnableSynceotid);

endmodule