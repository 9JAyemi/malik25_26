module half_adder_sva (
    input logic A,
    input logic B,
    input logic carry_out,
    input logic sum,
    input logic clk_in_14
);

property AddOneeotid; @(posedge clk_in_14) ( A ) != (  B ) |->  ( sum ) ==  ( A ^ B ) ;endproperty
assert property (AddOneeotid);

property CarryOnOneeotid; @(posedge clk_in_14) ( A ) == (  B )  |->  ( carry_out ) ==  ( A & B ) ;endproperty
assert property (CarryOnOneeotid);

endmodule