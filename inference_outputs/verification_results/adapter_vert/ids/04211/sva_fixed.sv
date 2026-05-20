module barrel_shifter_sva (
    input logic in,
    input logic out,
    input logic shift_amt,
    input logic shift_left,
    input logic b1,
    input logic clk_in_1
);

property ShiftLefteotid; @(posedge clk_in_1) (shift_left) |-> (out) == (in << shift_amt) ; endproperty
assert property (ShiftLefteotid);

property ShiftRighteotid; @(posedge clk_in_1) (shift_left) != 1'b1  |-> (out) == (in >> shift_amt) ; endproperty
assert property (ShiftRighteotid);

endmodule