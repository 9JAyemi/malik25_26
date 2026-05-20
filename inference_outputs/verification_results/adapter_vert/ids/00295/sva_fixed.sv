module top_module_sva (
    input logic A,
    input logic B,
    input logic opcode,
    input logic out,
    input logic result,
    input logic zero,
    input logic b000,
    input logic b0000,
    input logic b001,
    input logic b010,
    input logic b011,
    input logic b1,
    input logic b100,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (opcode) == (3'b000) |-> (out) == (A + B) ; endproperty
assert property (AddOneeotid);

property SubOneeotid; @(posedge clk_in_1) (opcode) == (3'b001) |-> (out) == (A - B) ; endproperty
assert property (SubOneeotid);

property ANDeotid; @(posedge clk_in_1) (opcode) == (3'b010) |-> (out) == (A & B) ; endproperty
assert property (ANDeotid);

property OReotid; @(posedge clk_in_1) (opcode) == (3'b011) |-> (out) == (A | B) ; endproperty
assert property (OReotid);

property XorOneeotid; @(posedge clk_in_1) (opcode) == (3'b100) |-> (out) == (A ^ B) ; endproperty
assert property (XorOneeotid);

property Zeroeotid; @(posedge clk_in_1) (result) == (4'b0000) |-> (zero) == 1'b1 ; endproperty
assert property (Zeroeotid);

endmodule