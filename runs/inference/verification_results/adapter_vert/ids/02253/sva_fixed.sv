module alu_sva (
    input logic a,
    input logic b,
    input logic op,
    input logic out,
    input logic b0,
    input logic b000,
    input logic b001,
    input logic b010,
    input logic b011,
    input logic b100,
    input logic b101,
    input logic clk_in_19
);

property AddOneeotid; @(posedge clk_in_19) (op) == (3'b000) |-> (out) == (a + b) ; endproperty
assert property (AddOneeotid);

property SubOneeotid; @(posedge clk_in_19) (op) == (3'b001) |-> (out) == (a - b) ; endproperty
assert property (SubOneeotid);

property AndOneeotid; @(posedge clk_in_19) (op) == (3'b010) |-> (out) == (a & b) ; endproperty
assert property (AndOneeotid);

property OrOneeotid; @(posedge clk_in_19) (op) == (3'b011) |-> (out) == (a | b) ; endproperty
assert property (OrOneeotid);

property XorOneeotid; @(posedge clk_in_19) (op) == (3'b100) |-> (out) == (a ^ b) ; endproperty
assert property (XorOneeotid);

property ShiftOneeotid; @(posedge clk_in_19) (op) == (3'b101) |-> (out) == ({a[2:0], 1'b0}) ; endproperty
assert property (ShiftOneeotid);

property SafeSynceotid; (op) != 3'b000 && (op) != 3'b001 && (op) != 3'b010 && (op) != 3'b011 && (op) != 3'b100 && (op) != 3'b101  |-> (out) == 4'b0 ; endproperty
assert property (SafeSynceotid);

endmodule