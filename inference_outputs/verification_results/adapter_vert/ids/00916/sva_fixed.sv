module calculator_sva (
    input logic a,
    input logic b,
    input logic op,
    input logic result,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (op) == (2'b00) |-> result == a + b ;endproperty
assert property (AddOneeotid);

property SubOneeotid; @(posedge clk_in_1) (op) == (2'b01) |-> result == a - b ;endproperty
assert property (SubOneeotid);

property MultOneeotid; @(posedge clk_in_1) (op) == (2'b10) |-> result == a * b ;endproperty
assert property (MultOneeotid);

property DivOneeotid; @(posedge clk_in_1) (op) == (2'b11) && (b != 0) |-> result == a / b ;endproperty
assert property (DivOneeotid);

endmodule