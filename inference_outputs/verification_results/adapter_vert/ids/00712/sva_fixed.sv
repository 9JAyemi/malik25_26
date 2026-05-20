module adder_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic clk_in_14
);

property AddOneeotid; @(posedge clk_in_14) ( A ) + ( B ) == ( C ) ; endproperty
assert property (AddOneeotid);

endmodule