module simple_counter_sva (
    input logic clk,
    input logic count,
    input logic en,
    input logic rst
);

property ResetSynceotid; @(posedge clk) (rst) |-> count == 0 ;endproperty
assert property (ResetSynceotid);

property EnableSynceotid; @(posedge clk) (en) && ! (rst)  |->  count == count + 1 ;endproperty
assert property (EnableSynceotid);

endmodule