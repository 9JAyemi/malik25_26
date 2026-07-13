module calculator_sva (
    input logic a,
    input logic b,
    input logic op,
    input logic result,
    input logic temp,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_1,
    input logic h00,
    input logic hFF
);

property AddOneeotid; @(posedge clk_in_1) (op) == (2'b00) |-> result == a + b ; endproperty
assert property (AddOneeotid);

property SubOneeotid; @(posedge clk_in_1) (op) == (2'b01) |-> result == a - b ; endproperty
assert property (SubOneeotid);

property Multeotid; @(posedge clk_in_1) (op) == (2'b10) |-> (temp) == (a * b) && ( (temp) > 8'hFF ) |-> result == 8'hFF ; endproperty
assert property (Multeotid);

property ValidDivideeotid; @(posedge clk_in_1) (op) == (2'b10) &&  ( !( (temp) > 8'hFF )  && ( (b) != 8'h00 ) )  |-> (temp) == (a / b) && ( (temp) > 8'hFF ) |-> result == 8'hFF ; endproperty
assert property (ValidDivideeotid);

property ValidDivideeotid_2; @(posedge clk_in_1) (op) == (2'b10) &&  ( !( (temp) > 8'hFF )  && ( (b) != 8'h00 ) )  |-> (temp) == (a / b) &&  ( (temp) <= 8'hFF )  |-> result == (temp) ; endproperty
assert property (ValidDivideeotid_2);

property SafeDivideeotid; @(posedge clk_in_1) (op) == (2'b11) &&  ( (b) == 8'h00 )  |-> result == 8'hFF ; endproperty
assert property (SafeDivideeotid);

endmodule