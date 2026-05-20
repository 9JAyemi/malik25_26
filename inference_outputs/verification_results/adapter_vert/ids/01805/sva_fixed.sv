module multiplier_sva (
    input logic num1,
    input logic num2,
    input logic product,
    input logic clk_in_1,
    input logic h00,
    input logic h0000,
    input logic hff,
    input logic hffff
);

property Multiplyeotid; @(posedge clk_in_1) (num1) * (num2) == (product) ;endproperty
assert property (Multiplyeotid);

property ValidDataeotid; @(posedge clk_in_1) (num1) != 8'hff &&  (num2) != 8'hff |-> (product) != 16'hffff ;endproperty
assert property (ValidDataeotid);

property ValidInputeotid; @(posedge clk_in_1) (num1) != 8'h00 &&  (num2) != 8'h00 |-> (product) != 16'h0000 ;endproperty
assert property (ValidInputeotid);

endmodule