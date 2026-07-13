module calculator_sva (
    input logic A,
    input logic B,
    input logic op,
    input logic result,
    input logic b00,
    input logic b0000000,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (op) == (2'b00) |-> result == A + B ; endproperty
assert property (AddOneeotid);

property SubOneeotid; @(posedge clk_in_1) (op) == (2'b01) |-> result == A - B ; endproperty
assert property (SubOneeotid);

property MultOneeotid; @(posedge clk_in_1) (op) == (2'b10) |-> result == A * B ; endproperty
assert property (MultOneeotid);

property SafeDivideeotid; @(posedge clk_in_1) (op) == (2'b11) && (B != 7'b0000000) |-> result == A / B ; endproperty
assert property (SafeDivideeotid);

property SafeDivideeotid_2; @(posedge clk_in_1) (op) == (2'b11) && (B == 7'b0000000) |-> result == 0 ; endproperty
assert property (SafeDivideeotid_2);

endmodule