// SVA for xor_gate
module xor_gate_sva(input logic a,b,out);
  // Functional equivalence on any input edge
  property p_xor_func;
    @(posedge a or negedge a or posedge b or negedge b)
    disable iff ($isunknown({a,b}))
      out === (a ^ b);
  endproperty
  a_xor_func: assert property(p_xor_func);

  // Single-input toggle implies output toggles
  property p_xor_toggle_a;
    @(posedge a or negedge a or posedge b or negedge b)
    disable iff ($isunknown({a,b,out}) || $isunknown($past({a,b,out})))
      ($changed(a) && $stable(b)) |-> (out != $past(out));
  endproperty
  a_xta: assert property(p_xor_toggle_a);

  property p_xor_toggle_b;
    @(posedge a or negedge a or posedge b or negedge b)
    disable iff ($isunknown({a,b,out}) || $isunknown($past({a,b,out})))
      ($changed(b) && $stable(a)) |-> (out != $past(out));
  endproperty
  a_xtb: assert property(p_xor_toggle_b);

  // Coverage: all input combinations observed
  c00: cover property(@(posedge a or negedge a or posedge b or negedge b) ! $isunknown({a,b}) && a==0 && b==0);
  c01: cover property(@(posedge a or negedge a or posedge b or negedge b) ! $isunknown({a,b}) && a==0 && b==1);
  c10: cover property(@(posedge a or negedge a or posedge b or negedge b) ! $isunknown({a,b}) && a==1 && b==0);
  c11: cover property(@(posedge a or negedge a or posedge b or negedge b) ! $isunknown({a,b}) && a==1 && b==1);
endmodule

// SVA for byte_reversal
module byte_reversal_sva(input logic [31:0] in, input logic [31:0] out);
  // Functional mapping (full and per-byte)
  always_comb begin
    if (!$isunknown(in)) assert (out === {in[7:0], in[15:8], in[23:16], in[31:24]});
    if (!$isunknown(in[7:0]))   assert (out[31:24] === in[7:0]);
    if (!$isunknown(in[15:8]))  assert (out[23:16] === in[15:8]);
    if (!$isunknown(in[23:16])) assert (out[15:8]  === in[23:16]);
    if (!$isunknown(in[31:24])) assert (out[7:0]   === in[31:24]);
    // Simple pattern coverage
    cover (in == 32'h00010203);
    cover (in == 32'hA55AF00F);
  end
endmodule

// SVA for functional_module
module functional_module_sva(input logic in1, input logic [31:0] in2, input logic [31:0] out);
  always_comb begin
    if (!$isunknown({in1,in2})) assert (out === (in2 | {31'b0,in1}));
    assert (out[31:1] === in2[31:1]);
    if (!$isunknown({in1,in2[0]})) assert (out[0] === (in2[0] | in1));
    // Coverage: key LSB cases
    cover (in1==0); cover (in1==1);
    cover (in2[0]==0); cover (in2[0]==1);
  end
endmodule

// SVA for top_module (checks internals and final mux behavior)
module top_module_sva(
  input logic a,b,select,
  input logic [31:0] in,
  input logic [31:0] out,
  input logic out_xor,
  input logic [31:0] byte_rev_out,
  input logic [31:0] func_out
);
  always_comb begin
    if (!$isunknown({a,b})) assert (out_xor === (a ^ b));
    if (!$isunknown(in)) assert (byte_rev_out === {in[7:0], in[15:8], in[23:16], in[31:24]});
    if (!$isunknown({out_xor,byte_rev_out})) assert (func_out === (byte_rev_out | {31'b0,out_xor}));
    if (!$isunknown({select,out_xor,func_out})) assert (out === (select ? func_out : {31'b0,out_xor}));

    if (!select) begin
      assert (out[31:1] === 31'b0);
      assert (out[0] === out_xor);
    end else begin
      assert (out[31:1] === byte_rev_out[31:1]);
      assert (out[0] === (byte_rev_out[0] | out_xor));
    end
  end

  // Branch/toggle coverage
  cover_select0: cover property (@(negedge select) 1);
  cover_select1: cover property (@(posedge select) 1);
  cover_axor0:   cover property (@(posedge a or negedge a or posedge b or negedge b) ! $isunknown({a,b}) && ((a^b)==0));
  cover_axor1:   cover property (@(posedge a or negedge a or posedge b or negedge b) ! $isunknown({a,b}) && ((a^b)==1));
endmodule

// Bind assertions to DUTs
bind xor_gate          xor_gate_sva          (.a(a), .b(b), .out(out));
bind byte_reversal     byte_reversal_sva     (.in(in), .out(out));
bind functional_module functional_module_sva (.in1(in1), .in2(in2), .out(out));
bind top_module        top_module_sva        (.a(a), .b(b), .select(select), .in(in), .out(out), .out_xor(out_xor), .byte_rev_out(byte_rev_out), .func_out(func_out));