module alu_sva (
    input logic A,
    input logic B,
    input logic alu_ctl,
    input logic result,
    input logic b0,
    input logic b0001,
    input logic b0010,
    input logic b0011,
    input logic b0100,
    input logic b0101,
    input logic b0110,
    input logic b0111,
    input logic b1000,
    input logic b1001,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (alu_ctl) == (4'b0001) |-> result == A + B ; endproperty
assert property (AddOneeotid);

property SubOneeotid; @(posedge clk_in_1) (alu_ctl) == (4'b0010) |-> result == A - B ; endproperty
assert property (SubOneeotid);

property AndOneeotid; @(posedge clk_in_1) (alu_ctl) == (4'b0011) |-> result == A & B ; endproperty
assert property (AndOneeotid);

property OrOneeotid; @(posedge clk_in_1) (alu_ctl) == (4'b0100) |-> result == A | B ; endproperty
assert property (OrOneeotid);

property XorOneeotid; @(posedge clk_in_1) (alu_ctl) == (4'b0101) |-> result == A ^ B ; endproperty
assert property (XorOneeotid);

property NotOrOneeotid; @(posedge clk_in_1) (alu_ctl) == (4'b0110) |-> result == ~(A | B) ; endproperty
assert property (NotOrOneeotid);

property RightShifteotid; @(posedge clk_in_1) (alu_ctl) == (4'b0111) |-> result == B >> 1 ; endproperty
assert property (RightShifteotid);

property ZeroCheckeotid; @(posedge clk_in_1) (alu_ctl) == (4'b1000) |-> result == {B[15:0], 16'b0} ; endproperty
assert property (ZeroCheckeotid);

property LessThaneotid; @(posedge clk_in_1) (alu_ctl) == (4'b1001) |-> result == (A < B) ; endproperty
assert property (LessThaneotid);

property ZeroCheckeotid_2; @(posedge clk_in_1) (alu_ctl) != 4'b0001 && @(posedge clk_in_1) (alu_ctl) != 4'b0010 && @(posedge clk_in_1) (alu_ctl) != 4'b0011 && @(posedge clk_in_1) (alu_ctl) != 4'b0100 && @(posedge clk_in_1) (alu_ctl) != 4'b0101 && @(posedge clk_in_1) (alu_ctl) != 4'b0110 && @(posedge clk_in_1) (alu_ctl) != 4'b0111 && @(posedge clk_in_1) (alu_ctl) != 4'b1000 && @(posedge clk_in_1) (alu_ctl) != 4'b1001  |-> result == 0; endproperty
assert property (ZeroCheckeotid_2);

endmodule