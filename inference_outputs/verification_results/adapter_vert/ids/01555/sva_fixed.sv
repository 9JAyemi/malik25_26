module barrel_shifter_sva (
    input logic dir,
    input logic in,
    input logic out,
    input logic shift,
    input logic clk_in_1
);

property LeftShiftsOnRiseeotid; @(posedge clk_in_1) (dir) == (0) |-> (out) == (in << shift); endproperty
assert property (LeftShiftsOnRiseeotid);

property RightShiftsOnRiseeotid; @(posedge clk_in_1) (dir) != 0 |-> (out) == (in >> shift); endproperty
assert property (RightShiftsOnRiseeotid);

endmodule