module counter_4bit_sva (
    input logic clk,
    input logic count,
    input logic enable,
    input logic reset,
    input logic b0,
    input logic reg_13
);

property ResetSynceotid; @(posedge clk) (reset) |-> (count == 4'b0); endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (reset) &&  (enable) |-> (count == reg_13); endproperty
assert property (ResetSynceotid_2);

endmodule