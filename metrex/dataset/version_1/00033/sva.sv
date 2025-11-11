// SVA for top_module (bindable, concise, quality-focused)

`ifndef TOP_MODULE_SVA
`define TOP_MODULE_SVA

module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [3:0]  in,
  input  logic        a,
  input  logic        b,
  input  logic        out_and,
  input  logic        out_or,
  input  logic        out_xor,
  input  logic        xor_gate_out,
  input  logic        final_out
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Combinational correctness of derived signals (LSB-intended semantics)
  assert property (out_and == ((in[0] & in[1]) & (in[2] & in[3])));
  assert property (out_or  == ((in[0] | in[1]) | (in[2] | in[3])));
  assert property (out_xor == ((in[0] ^ in[1]) ^ (in[2] ^ in[3])));
  assert property (xor_gate_out == (a ^ b));

  // Async reset behavior and reset hold
  assert property (@(posedge reset) final_out == 1'b0);
  assert property (reset |-> final_out == 1'b0);

  // Registered update: next-cycle value equals previous-cycle expression
  assert property (!reset && !$past(reset) |-> 
                   final_out == $past((out_and & out_or) ^ (out_xor ^ xor_gate_out)));

  // Sanity: no X/Z on key signals at clock edge
  assert property (!$isunknown({out_and, out_or, out_xor, xor_gate_out, final_out}));

  // Minimal functional coverage
  cover property (!reset && out_and);
  cover property (!reset && !out_and);
  cover property (!reset && out_or);
  cover property (!reset && !out_or);
  cover property (!reset && out_xor);
  cover property (!reset && !out_xor);
  cover property (!reset && final_out);
  cover property (!reset && !final_out);

  cover property ({a,b} == 2'b00);
  cover property ({a,b} == 2'b01);
  cover property ({a,b} == 2'b10);
  cover property ({a,b} == 2'b11);

  cover property (reset ##1 !reset); // reset pulse observed
endmodule

bind top_module top_module_sva sva_i (
  .clk(clk),
  .reset(reset),
  .in(in),
  .a(a),
  .b(b),
  .out_and(out_and),
  .out_or(out_or),
  .out_xor(out_xor),
  .xor_gate_out(xor_gate_out),
  .final_out(final_out)
);

`endif