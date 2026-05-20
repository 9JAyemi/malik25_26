module barrel_shifter_sva (
    input logic dir,
    input logic in,
    input logic out,
    input logic shift,
    input logic shifted_data_1,
    input logic shifted_data_2,
    input logic clk_in_1,
    input logic h0,
    input logic h3
);

property ShiftIneotid; @(posedge clk_in_1) (dir) |-> (shifted_data_1) == (in << shift) ; endproperty
assert property (ShiftIneotid);

property ShiftOuteotid; @(posedge clk_in_1) (dir) &&  (  (shift) != 6'h3  ||  (in) != 16'h0  ||  (shifted_data_1) != 16'h0 )  |-> (shifted_data_2) == (shifted_data_1 << shift) ; endproperty
assert property (ShiftOuteotid);

property ShiftIneotid_2; @(posedge clk_in_1) (dir) |-> (out) == (shifted_data_2) ; endproperty
assert property (ShiftIneotid_2);

endmodule