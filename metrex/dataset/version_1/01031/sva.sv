// SVA for xor_gate and top_module
// Bind these into the DUT; no DUT edits required.

module xor_gate_sva;
  // Accesses xor_gate internals by name when bound.
  // Functional equivalence (XNOR), structure, exclusivity, and known-ness.
  always_comb begin
    assert (out === ~(a ^ b)) else $error("xor_gate: out != ~(a^b)");
    assert (w1 === (a & ~b)) else $error("xor_gate: w1 != a & ~b");
    assert (w2 === (~a & b)) else $error("xor_gate: w2 != ~a & b");
    assert (w3 === (w1 | w2)) else $error("xor_gate: w3 != w1 | w2");
    assert (out === ~w3) else $error("xor_gate: out != ~w3");
    assert ($onehot0({w1,w2})) else $error("xor_gate: {w1,w2} not onehot0");

    if (!$isunknown({a,b})) begin
      assert (!$isunknown(out)) else $error("xor_gate: out X/Z with known inputs");
    end

    // Basic truth-table coverage
    cover ({a,b,out} === 3'b001); // a=0,b=0 -> out=1
    cover ({a,b,out} === 3'b010); // a=0,b=1 -> out=0
    cover ({a,b,out} === 3'b100); // a=1,b=0 -> out=0
    cover ({a,b,out} === 3'b111); // a=1,b=1 -> out=1
  end
endmodule

module top_module_sva;
  // Pipeline correctness relative to primary inputs (one-cycle latency)
  property p_func_xnor_prev_inputs;
    @(posedge clk) out_always_ff === ~( $past(a,1,1'b0) ^ $past(b,1,1'b0) );
  endproperty
  assert property (p_func_xnor_prev_inputs)
    else $error("top: out_always_ff != ~(past(a)^past(b))");

  // Registered captures and combinational relation after NBA settle
  assert property (@(posedge clk) ##0 a_ff === $past(a,1,1'b0))
    else $error("top: a_ff != past(a)");
  assert property (@(posedge clk) ##0 b_ff === $past(b,1,1'b0))
    else $error("top: b_ff != past(b)");
  assert property (@(posedge clk) ##0 out_always_ff === ~(a_ff ^ b_ff))
    else $error("top: out_always_ff != ~(a_ff^b_ff)");

  // Known-ness: known past inputs imply known output
  assert property (@(posedge clk)
                   !$isunknown($past({a,b},1)) |-> !$isunknown(out_always_ff))
    else $error("top: out_always_ff X/Z with known past inputs");

  // Functional coverage of all input combinations (as seen at past cycle)
  cover property (@(posedge clk) $past({a,b},1) == 2'b00 && out_always_ff==1'b1);
  cover property (@(posedge clk) $past({a,b},1) == 2'b01 && out_always_ff==1'b0);
  cover property (@(posedge clk) $past({a,b},1) == 2'b10 && out_always_ff==1'b0);
  cover property (@(posedge clk) $past({a,b},1) == 2'b11 && out_always_ff==1'b1);

  // Output toggling coverage
  cover property (@(posedge clk) out_always_ff ##1 !out_always_ff);
  cover property (@(posedge clk) !out_always_ff ##1 out_always_ff);
endmodule

bind xor_gate    xor_gate_sva    xor_gate_sva_i();
bind top_module  top_module_sva  top_module_sva_i();