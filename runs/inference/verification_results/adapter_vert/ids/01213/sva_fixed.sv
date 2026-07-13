module barrel_shifter_sva (
    input logic DATA,
    input logic SHIFTED_DATA,
    input logic SHIFT_AMOUNT,
    input logic SHIFT_DIRECTION,
    input logic clk_in_11
);

property ShiftLefteotid; @(posedge clk_in_11) (SHIFT_DIRECTION) == (0) |-> (SHIFTED_DATA) == (DATA << SHIFT_AMOUNT) ; endproperty
assert property (ShiftLefteotid);

property ShiftRighteotid; @(posedge clk_in_11) (SHIFT_DIRECTION) != 0 |-> (SHIFTED_DATA) == (DATA >> SHIFT_AMOUNT) ; endproperty
assert property (ShiftRighteotid);

endmodule