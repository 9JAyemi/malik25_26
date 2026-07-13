module alu_sva (
    input logic a,
    input logic aluc,
    input logic b,
    input logic result,
    input logic b0,
    input logic clk_in_1,
    input logic d0,
    input logic d1,
    input logic d10,
    input logic d11,
    input logic d12,
    input logic d14,
    input logic d2,
    input logic d3,
    input logic d31,
    input logic d4,
    input logic d5,
    input logic d6,
    input logic d7,
    input logic d8,
    input logic d9
);

property AddSynceotid; @(posedge clk_in_1) (aluc) == (5'd0) |-> result == a + b ; endproperty
assert property (AddSynceotid);

property AddSynceotid_2; @(posedge clk_in_1) (aluc) == (5'd1) |-> result == a + b ; endproperty
assert property (AddSynceotid_2);

property SubSynceotid; @(posedge clk_in_1) (aluc) == (5'd2) |-> result == a - b ; endproperty
assert property (SubSynceotid);

property SubSynceotid_2; @(posedge clk_in_1) (aluc) == (5'd3) |-> result == a - b ; endproperty
assert property (SubSynceotid_2);

property ANDeotid; @(posedge clk_in_1) (aluc) == (5'd4) |-> result == a & b ; endproperty
assert property (ANDeotid);

property OReotid; @(posedge clk_in_1) (aluc) == (5'd5) |-> result == a | b ; endproperty
assert property (OReotid);

property XOrEeotid; @(posedge clk_in_1) (aluc) == (5'd6) |-> result == a ^ b ; endproperty
assert property (XOrEeotid);

property ORNOReotid; @(posedge clk_in_1) (aluc) == (5'd7) |-> result == ~(a | b) ; endproperty
assert property (ORNOReotid);

property SetLesseotid; @(posedge clk_in_1) (aluc) == (5'd8) |-> result == (a[31]^b[31])?(a[31]?1:0):(a<b) ; endproperty
assert property (SetLesseotid);

property SetLesseotid_2; @(posedge clk_in_1) (aluc) == (5'd9) |-> result == a < b ; endproperty
assert property (SetLesseotid_2);

property ShiftLefteotid; @(posedge clk_in_1) (aluc) == (5'd10) |-> result == b << a ; endproperty
assert property (ShiftLefteotid);

property ShiftRighteotid; @(posedge clk_in_1) (aluc) == (5'd11) |-> result == b >> a ; endproperty
assert property (ShiftRighteotid);

property ShiftRightArithmeticeotid; @(posedge clk_in_1) (aluc) == (5'd12) |-> result == $signed(b) >>> a ; endproperty
assert property (ShiftRightArithmeticeotid);

property LoadUpeotid; @(posedge clk_in_1) (aluc) == (5'd14) |-> result == {b[15:0], 16'b0} ; endproperty
assert property (LoadUpeotid);

property Zeroeotid; @(posedge clk_in_1) (aluc) == (5'd31) |-> result == 0 ; endproperty
assert property (Zeroeotid);

property ValidInputeotid; @(posedge clk_in_1) (aluc) != 5'd0 && @(posedge clk_in_1) (aluc) != 5'd1 && @(posedge clk_in_1) (aluc) != 5'd2 && @(posedge clk_in_1) (aluc) != 5'd3 && @(posedge clk_in_1) (aluc) != 5'd4 && @(posedge clk_in_1) (aluc) != 5'd5 && @(posedge clk_in_1) (aluc) != 5'd6 && @(posedge clk_in_1) (aluc) != 5'd7 && @(posedge clk_in_1) (aluc) != 5'd8 && @(posedge clk_in_1) (aluc) != 5'd9 && @(posedge clk_in_1) (aluc) != 5'd10 && @(posedge clk_in_1) (aluc) != 5'd11 && @(posedge clk_in_1) (aluc) != 5'd12 && @(posedge clk_in_1) (aluc) != 5'd14 && @(posedge clk_in_1) (aluc) != 5'd31  |-> result == 0; endproperty
assert property (ValidInputeotid);

endmodule