// SVA for top_module
module top_module_sva (
  input logic        clk,
  input logic        d,
  input logic [31:0] in,
  input logic        q,
  input logic [31:0] out_xor,
  input logic [31:0] out_and,
  input logic [31:0] out_final
);
  default clocking cb @(posedge clk); endclocking

  // past-valid for $past safety
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Sequential: q is d delayed by 1 cycle
  assert property (past_valid && !$isunknown($past(d)) |-> q == $past(d));

  // Combinational widths: upper halves are zero-extended
  assert property (out_xor[31:16] == 16'h0);
  assert property (out_and[31:16] == 16'h0);

  // Functional lower halves when inputs are known
  assert property (!$isunknown(in) |-> out_xor[15:0] == (in[31:16] ^ in[15:0]));
  assert property (!$isunknown(in) |-> out_and[15:0] == (in[31:16] & in[15:0]));

  // Identity: (a^b)&(a&b) == 0 per bit -> out_final reduces to {32{q}} when inputs known
  assert property (out_final[31:16] == {16{q}});
  assert property (!$isunknown(in) |-> out_final[15:0] == {16{q}});
  assert property (!$isunknown(in) |-> ((out_xor & out_and) == 32'h0));

  // Coverage
  cover property (past_valid && $rose(q));
  cover property (past_valid && $fell(q));
  cover property (out_xor[15:0] == 16'h0000);
  cover property (out_xor[15:0] == 16'hFFFF);
  cover property (out_and[15:0] == 16'h0000);
  cover property (out_and[15:0] != 16'h0000);
  cover property ((out_xor[15:0] != 16'h0000) && (out_and[15:0] != 16'h0000));
  cover property (out_final == 32'h0000_0000);
  cover property (out_final == 32'hFFFF_FFFF);
endmodule

bind top_module top_module_sva sva_i (.*);