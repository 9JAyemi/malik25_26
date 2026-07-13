module alu_16bit_sva (
    input logic A,
    input logic B,
    input logic Y,
    input logic notA,
    input logic op,
    input logic b0,
    input logic b0000,
    input logic b0001,
    input logic b0010,
    input logic b0011,
    input logic b0100,
    input logic b0101,
    input logic b0110,
    input logic b0111,
    input logic b1000,
    input logic b1001,
    input logic bxxxx,
    input logic clk_in_1,
    input logic rotateLeft,
    input logic rotateRight,
    input logic shiftLeft,
    input logic shiftRight
);

property AddOneeotid; @(posedge clk_in_1) (op) == (4'b0000) |-> (Y) == (A + B) ; endproperty
assert property (AddOneeotid);

property SubOneeotid; @(posedge clk_in_1) (op) == (4'b0001) |-> (Y) == (A - B) ; endproperty
assert property (SubOneeotid);

property AndOneeotid; @(posedge clk_in_1) (op) == (4'b0010) |-> (Y) == (A & B) ; endproperty
assert property (AndOneeotid);

property OrOneeotid; @(posedge clk_in_1) (op) == (4'b0011) |-> (Y) == (A | B) ; endproperty
assert property (OrOneeotid);

property XorOneeotid; @(posedge clk_in_1) (op) == (4'b0100) |-> (Y) == (A ^ B) ; endproperty
assert property (XorOneeotid);

property NotOneeotid; @(posedge clk_in_1) (op) == (4'b0101) |-> (Y) == (notA) ; endproperty
assert property (NotOneeotid);

property ShiftLeftOneeotid; @(posedge clk_in_1) (op) == (4'b0110) |-> (Y) == (shiftLeft) ; endproperty
assert property (ShiftLeftOneeotid);

property ShiftRightOneeotid; @(posedge clk_in_1) (op) == (4'b0111) |-> (Y) == (shiftRight) ; endproperty
assert property (ShiftRightOneeotid);

property RotateLeftOneeotid; @(posedge clk_in_1) (op) == (4'b1000) |-> (Y) == (rotateLeft) ; endproperty
assert property (RotateLeftOneeotid);

property RotateRightOneeotid; @(posedge clk_in_1) (op) == (4'b1001) |-> (Y) == (rotateRight) ; endproperty
assert property (RotateRightOneeotid);

property ValidOpseotid; @(posedge clk_in_1) (op) != 4'bxxxx  |-> (Y) != 16'b0; endproperty
assert property (ValidOpseotid);

endmodule