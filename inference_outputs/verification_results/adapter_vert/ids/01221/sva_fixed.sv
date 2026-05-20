module alu_sva (
    input logic A,
    input logic B,
    input logic opcode,
    input logic out,
    input logic zero,
    input logic b0,
    input logic b000,
    input logic b0000,
    input logic b001,
    input logic b010,
    input logic b011,
    input logic b1,
    input logic b100,
    input logic b101,
    input logic b110,
    input logic b111,
    input logic clk_in_19
);

property AddOneeotid; @(posedge clk_in_19) (opcode) == (3'b000) |-> (out) == (A + B) ; endproperty
assert property (AddOneeotid);

property SubOneeotid; @(posedge clk_in_19) (opcode) == (3'b001) |-> (out) == (A - B) ; endproperty
assert property (SubOneeotid);

property ANDeotid; @(posedge clk_in_19) (opcode) == (3'b010) |-> (out) == (A & B) ; endproperty
assert property (ANDeotid);

property OReotid; @(posedge clk_in_19) (opcode) == (3'b011) |-> (out) == (A | B) ; endproperty
assert property (OReotid);

property XOrEeotid; @(posedge clk_in_19) (opcode) == (3'b100) |-> (out) == (A ^ B) ; endproperty
assert property (XOrEeotid);

property ShiftLeftOneeotid; @(posedge clk_in_19) (opcode) == (3'b101) |-> (out) == (A << 1) ; endproperty
assert property (ShiftLeftOneeotid);

property ShiftRightOneeotid; @(posedge clk_in_19) (opcode) == (3'b110) |-> (out) == (A >> 1) ; endproperty
assert property (ShiftRightOneeotid);

property NotAeotid; @(posedge clk_in_19) (opcode) == (3'b111) |-> (out) == (~A) ; endproperty
assert property (NotAeotid);

property ZeroCheckeotid; @(posedge clk_in_19) (out) == 4'b0000 |-> (zero) == 1'b1 ; endproperty
assert property (ZeroCheckeotid);

property Safeeotid; @(posedge clk_in_19) (out) != 4'b0000 |-> (zero) == 1'b0 ; endproperty
assert property (Safeeotid);

endmodule