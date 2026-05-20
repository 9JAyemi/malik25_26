module shift_right_sva (
    input logic clk,
    input logic ld,
    input logic out,
    input logic rst,
    input logic shift,
    input logic shiftreg,
    input logic x,
    input logic b0,
    input logic b1
);

property ResetSynceotid; @(posedge clk) (rst) |-> shiftreg == 0 && out == 1'b0 ;endproperty
assert property (ResetSynceotid);

property LoadSynceotid; @(posedge clk) (rst) != 1'b1 && (ld) |-> shiftreg == x && out == 1'b0 ;endproperty
assert property (LoadSynceotid);

property ShiftOneotid; @(posedge clk) (rst) != 1'b1 && !(ld)  && (shift) |-> out == shiftreg[0] && shiftreg == {1'b0,shiftreg[63:1]};endproperty
assert property (ShiftOneotid);

endmodule