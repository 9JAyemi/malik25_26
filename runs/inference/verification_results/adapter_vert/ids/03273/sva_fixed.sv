module bitwise_operations_sva (
    input logic and_result,
    input logic operation_select,
    input logic or_result,
    input logic result,
    input logic shift_result,
    input logic xor_result,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_1
);

property BitwiseAndeotid; @(posedge clk_in_1) (operation_select) == (2'b00) |-> result == and_result ; endproperty
assert property (BitwiseAndeotid);

property BitwiseOreotid; @(posedge clk_in_1) (operation_select) == (2'b01) |-> result == or_result ; endproperty
assert property (BitwiseOreotid);

property BitwiseXorEeotid; @(posedge clk_in_1) (operation_select) == (2'b10) |-> result == xor_result ; endproperty
assert property (BitwiseXorEeotid);

property ShiftOnClockeotid; @(posedge clk_in_1) (operation_select) == (2'b11) |-> result == shift_result ; endproperty
assert property (ShiftOnClockeotid);

endmodule