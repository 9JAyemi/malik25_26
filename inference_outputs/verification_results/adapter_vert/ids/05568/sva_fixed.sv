module calculator_sva (
    input logic num1,
    input logic num2,
    input logic op,
    input logic result,
    input logic b00,
    input logic b00000000,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (op) == (2'b00) |-> (result) == (num1 + num2) ; endproperty
assert property (AddOneeotid);

property SubOneeotid; @(posedge clk_in_1) (op) == (2'b01) |-> (result) == (num1 - num2) ; endproperty
assert property (SubOneeotid);

property MultOneeotid; @(posedge clk_in_1) (op) == (2'b10) |-> (result) == (num1 * num2) ; endproperty
assert property (MultOneeotid);

property DivOneeotid; @(posedge clk_in_1) (op) == (2'b11) && (  !(num2)  ) |-> (result) == 8'b00000000 ; endproperty
assert property (DivOneeotid);

property SafeDivideeotid; @(posedge clk_in_1) (op) == (2'b11) && (  (num2)  ) |-> (result) == (num1 / num2) ; endproperty
assert property (SafeDivideeotid);

endmodule