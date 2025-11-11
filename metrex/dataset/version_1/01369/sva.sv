// SVA checker for majority_circuit
module majority_circuit_sva (input logic a, b, c, input logic out);

  // Helpers
  let known_in = !$isunknown({a,b,c});
  let maj      = (a & b) | (b & c) | (c & a);

  // Functional correctness (combinational, zero-latency when inputs known)
  assert property (@(a or b or c or out) known_in |-> (out === maj))
    else $error("majority_circuit: out != majority(a,b,c)");

  // No spurious output changes without input change
  assert property (@(a or b or c or out) $changed(out) |-> ($changed(a) or $changed(b) or $changed(c)))
    else $error("majority_circuit: out changed without input change");

  // Local consistency: if any two inputs equal, out must equal them (when inputs known)
  assert property (@(a or b or c or out) known_in && (a===b) |-> (out===a));
  assert property (@(a or b or c or out) known_in && (b===c) |-> (out===b));
  assert property (@(a or b or c or out) known_in && (c===a) |-> (out===c));

  // Out must be known when inputs are known
  assert property (@(a or b or c or out) known_in |-> !$isunknown(out));

  // Functional coverage: all input combinations observed
  cover property (@(a or b or c or out) (a==0 && b==0 && c==0));
  cover property (@(a or b or c or out) (a==0 && b==0 && c==1));
  cover property (@(a or b or c or out) (a==0 && b==1 && c==0));
  cover property (@(a or b or c or out) (a==0 && b==1 && c==1));
  cover property (@(a or b or c or out) (a==1 && b==0 && c==0));
  cover property (@(a or b or c or out) (a==1 && b==0 && c==1));
  cover property (@(a or b or c or out) (a==1 && b==1 && c==0));
  cover property (@(a or b or c or out) (a==1 && b==1 && c==1));

  // Output activity coverage
  cover property (@(a or b or c or out) !$isunknown(out) && $rose(out));
  cover property (@(a or b or c or out) !$isunknown(out) && $fell(out));

endmodule

// Bind into the DUT
bind majority_circuit majority_circuit_sva sva (.a(a), .b(b), .c(c), .out(out));