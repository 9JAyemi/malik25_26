// SVA for xor_gate and m_xor_gate (concise, full functional coverage)

`ifndef XOR_SVA
`define XOR_SVA

// Checker for structural xor_gate (has internal net xored)
module xor_gate_chk(input logic a, b, out, xored);

  // Functional correctness (sample after delta to avoid preponed race)
  a_truth: assert property (@(a or b)
    1'b1 |-> ##0 (out === (a ^ b)));

  // Internal net and buffer consistency
  a_pipe:  assert property (@(a or b)
    1'b1 |-> ##0 (xored === (a ^ b) && out === xored));

  // No X/Z on outputs when inputs are known
  a_no_x:  assert property (@(a or b)
    (!$isunknown({a,b})) |-> ##0 (!$isunknown({xored,out})));

  // Functional coverage: all input combinations and corresponding outputs
  c00: cover property (@(a or b) ##0 (a===0 && b===0 && out===0));
  c01: cover property (@(a or b) ##0 (a===0 && b===1 && out===1));
  c10: cover property (@(a or b) ##0 (a===1 && b===0 && out===1));
  c11: cover property (@(a or b) ##0 (a===1 && b===1 && out===0));

  // Output activity coverage
  c_out_toggle: cover property (@(a or b) ##0 $changed(out));

endmodule

bind xor_gate xor_gate_chk xor_gate_chk_i (.a(a), .b(b), .out(out), .xored(xored));

// Checker for behavioral m_xor_gate
module m_xor_gate_chk(input logic a, b, out);

  a_truth: assert property (@(a or b)
    1'b1 |-> ##0 (out === (a ^ b)));

  a_no_x:  assert property (@(a or b)
    (!$isunknown({a,b})) |-> ##0 (!$isunknown(out)));

  c00: cover property (@(a or b) ##0 (a===0 && b===0 && out===0));
  c01: cover property (@(a or b) ##0 (a===0 && b===1 && out===1));
  c10: cover property (@(a or b) ##0 (a===1 && b===0 && out===1));
  c11: cover property (@(a or b) ##0 (a===1 && b===1 && out===0));

  c_out_toggle: cover property (@(a or b) ##0 $changed(out));

endmodule

bind m_xor_gate m_xor_gate_chk m_xor_gate_chk_i (.a(a), .b(b), .out(out));

`endif