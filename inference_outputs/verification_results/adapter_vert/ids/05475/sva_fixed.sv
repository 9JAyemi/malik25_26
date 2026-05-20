module barrel_shifter_sva (
    input logic dir,
    input logic in,
    input logic out,
    input logic shift_amt,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic clk_in_1
);

property ShiftSynceotid; @(posedge clk_in_1) (shift_amt) == (2'b00) |-> (out) == (in); endproperty
assert property (ShiftSynceotid);

property ShiftRighteotid; @(posedge clk_in_1) (shift_amt) == (2'b01) &&  ( dir ) |-> (out) == ({in[2:0], in[3]}); endproperty
assert property (ShiftRighteotid);

property ShiftRighteotid_2; @(posedge clk_in_1) (shift_amt) == (2'b01) &&  ( !(dir) ) |-> (out) == ({in[1:0], in[3:2]}); endproperty
assert property (ShiftRighteotid_2);

property ShiftLefteotid; @(posedge clk_in_1) (shift_amt) == (2'b10) &&  ( !(dir) ) |-> (out) == ({in[1:0], in[3:2]}); endproperty
assert property (ShiftLefteotid);

property ShiftLefteotid_2; @(posedge clk_in_1) (shift_amt) == (2'b10) &&  (  (dir) ) |-> (out) == ({in[2:0], in[3]}); endproperty
assert property (ShiftLefteotid_2);

property ShiftOneeotid; @(posedge clk_in_1) (shift_amt) == (2'b11) |-> (out) == ({in[0], in[3:1]}); endproperty
assert property (ShiftOneeotid);

endmodule