module arithmetic_op_sva (
    input logic a,
    input logic b,
    input logic ctrl,
    input logic result,
    input logic b0,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic clk_in_1
);

property AddSynceotid; @(posedge clk_in_1) (ctrl) == (2'b00) |-> result == a + b ; endproperty
assert property (AddSynceotid);

property SubSynceotid; @(posedge clk_in_1) (ctrl) == (2'b01) |-> result == a - b ; endproperty
assert property (SubSynceotid);

property XorSynceotid; @(posedge clk_in_1) (ctrl) == (2'b10) |-> result == a ^ b ; endproperty
assert property (XorSynceotid);

property ValidCtrleotid; @(posedge clk_in_1) (ctrl) != 2'b00 && @(posedge clk_in_1) (ctrl) != 2'b01 && @(posedge clk_in_1) (ctrl) != 2'b10  |-> result == 8'b0; endproperty
assert property (ValidCtrleotid);

endmodule