module register_sva (
    input logic clk,
    input logic xclear,
    input logic xin,
    input logic xload,
    input logic xout
);

property ResetSynceotid; @(posedge clk) (xclear) |-> xout == 0 ;endproperty
assert property (ResetSynceotid);

property LoadSynceotid; @(posedge clk) (xload) |-> xout == xin ;endproperty
assert property (LoadSynceotid);

endmodule