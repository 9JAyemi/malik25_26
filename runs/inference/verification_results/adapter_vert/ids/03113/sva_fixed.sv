module addition_module_sva (
    input logic A,
    input logic B,
    input logic carry,
    input logic temp_sum,
    input logic b0,
    input logic b1,
    input logic bxxxxxx1x,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (A) + (B) == (temp_sum) ; endproperty
assert property (AddOneeotid);

property CarryCheckeotid; @(posedge clk_in_1) (temp_sum) == (8'bxxxxxx1x) |-> (carry) == (1'b1) ; endproperty
assert property (CarryCheckeotid);

property ValidSumeotid; @(posedge clk_in_1) (temp_sum) != 8'bxxxxxx1x |-> (carry) == (1'b0) ; endproperty
assert property (ValidSumeotid);

endmodule