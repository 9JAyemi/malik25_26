module split_16bit_input_sva (
    input logic clk,
    input logic in,
    input logic out_hi,
    input logic out_lo
);

property SplitIneotid; @(posedge clk) ( in ) |-> ( out_hi ) == ( in[15:8] ) ; endproperty
assert property (SplitIneotid);

property SplitLoeotid; @(posedge clk) ( in ) |-> ( out_lo ) == ( in[7:0] ) ; endproperty
assert property (SplitLoeotid);

endmodule