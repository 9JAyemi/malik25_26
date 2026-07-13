module binary_counter_sva (
    input logic COUNT,
    input logic EN,
    input logic RST,
    input logic clk,
    input logic b0,
    input logic b0000,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (RST) |-> (COUNT) == 4'b0000 ;endproperty
assert property (ResetSynceotid);

property EnableSynceotid; @(posedge clk) (RST) != 1'b0 &&  (EN)  |-> (COUNT) == (COUNT) + 1'b1 ;endproperty
assert property (EnableSynceotid);

endmodule