module four_bit_adder_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic Cout,
    input logic S,
    input logic b1111,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (A) + (B) == (S) ;endproperty
assert property (AddOneeotid);

property AddOneeotid_2; @(posedge clk_in_1) (A) + (B) > 4'b1111 |-> (C) ;endproperty
assert property (AddOneeotid_2);

property CarryOneeotid; @(posedge clk_in_1) (A) + (B) > 4'b1111 |-> (Cout) ;endproperty
assert property (CarryOneeotid);

endmodule