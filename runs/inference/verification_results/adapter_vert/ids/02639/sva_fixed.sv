module my_mac_sva (
    input logic ce,
    input logic clk,
    input logic din0,
    input logic din1,
    input logic dout,
    input logic reset
);

property ResetSynceotid; @(posedge clk) (reset) |-> dout == 0 ;endproperty
assert property (ResetSynceotid);

property ValidCeotid; @(posedge clk) (ce) && !(reset) |-> dout == dout + din0 * din1 ;endproperty
assert property (ValidCeotid);

endmodule