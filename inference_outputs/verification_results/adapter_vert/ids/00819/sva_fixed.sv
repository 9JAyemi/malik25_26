module and4_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X,
    input logic X1,
    input logic X2,
    input logic clk_in_1
);

property ValidIneotid; @(posedge clk_in_1) (A) && (B) && (C) |-> X1 ;endproperty
assert property (ValidIneotid);

property ValidIneotid_2; @(posedge clk_in_1) (C) && (D) |-> X2 ;endproperty
assert property (ValidIneotid_2);

property ValidXeotid; @(posedge clk_in_1) (X1) && (X2)  |->  (X) ;endproperty
assert property (ValidXeotid);

endmodule