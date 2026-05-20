module dffl_64_sva (
    input logic clk,
    input logic d,
    input logic ld,
    input logic q,
    input logic rst,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (rst) |-> q == 0 ;endproperty
assert property (ResetSynceotid);

property LoadSynceotid; @(posedge clk) (rst) != 1'b1 &&  (ld) |-> q == d ;endproperty
assert property (LoadSynceotid);

endmodule