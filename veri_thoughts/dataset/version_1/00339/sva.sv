// SVA for xor_system and leaf cells. Bind these into the DUTs.

// Top-level checker
module xor_system_sva (
  input logic a,
  input logic b,
  input logic out,
  input logic not_a,
  input logic not_b,
  input logic not_a_b
);
  default clocking cb @(*); endclocking

  // Leaf equivalences inside xor_system
  a_inv_ok:   assert property (not_a   === ~a)           else $error("not_a must be ~a");
  b_inv_ok:   assert property (not_b   === ~b)           else $error("not_b must be ~b");
  path1_ok:   assert property (not_a_b === (a ^ not_b))  else $error("not_a_b must be a ^ ~b");
  path2_ok:   assert property (out     === (not_a ^ b))  else $error("out must be ~a ^ b");

  // Functional intent: out is XNOR of a and b
  func_ok:    assert property (out === (a ~^ b))         else $error("out must be a ~^ b (XNOR)");

  // Both XOR paths should agree when inputs are known (catches multi-drive/loop)
  paths_agree_when_known:
               assert property ((!$isunknown({a,b})) |-> (out === not_a_b))
               else $error("XOR paths disagree with known inputs");

  // No X/Z on internal nets/out when inputs are known
  known_propagation:
               assert property ((!$isunknown({a,b})) |-> !$isunknown({not_a,not_b,not_a_b,out}))
               else $error("X/Z observed on internal nets/out with known inputs");

  // Truth-table coverage for XNOR at top level
  cover_00:   cover property (!a && !b &&  out);
  cover_01:   cover property (!a &&  b && !out);
  cover_10:   cover property ( a && !b && !out);
  cover_11:   cover property ( a &&  b &&  out);
endmodule

bind xor_system xor_system_sva sva_xor_system (
  .a(a), .b(b), .out(out),
  .not_a(not_a), .not_b(not_b), .not_a_b(not_a_b)
);

// Checker for not_gate leaf
module not_gate_sva (input logic in, input logic out);
  default clocking @(*); endclocking
  assert property (out === ~in) else $error("not_gate: out != ~in");
  cover property ($changed(out));
endmodule
bind not_gate not_gate_sva sva_not (.in(in), .out(out));

// Checker for xor_gate leaf
module xor_gate_sva (input logic a, input logic b, input logic out);
  default clocking @(*); endclocking
  assert property (out === (a ^ b)) else $error("xor_gate: out != a ^ b");
  // Truth-table coverage for XOR cell
  cover property (!a && !b && !out);
  cover property (!a &&  b &&  out);
  cover property ( a && !b &&  out);
  cover property ( a &&  b && !out);
endmodule
bind xor_gate xor_gate_sva sva_xor (.a(a), .b(b), .out(out));