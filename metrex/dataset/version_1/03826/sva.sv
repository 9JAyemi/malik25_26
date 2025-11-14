// SVA for module 'complex'. Bind this checker to the DUT.
// Usage: bind complex complex_sva svacheck();

module complex_sva;
  // Bound into scope of 'complex'; can see x,y,and_outputs,or_outputs,out.
  default clocking cb @(*); endclocking
  default disable iff ($isunknown({x,y}));

  // Leaf ANDs
  genvar i;
  generate
    for (i=0; i<8; i++) begin : g_and_checks
      assert property (and_outputs[i] == (x[i] & y[i]))
        else $error("and_outputs[%0d] mismatch", i);
      cover property (and_outputs[i]);
    end
    // Pairwise ORs
    for (i=0; i<4; i++) begin : g_or_checks
      assert property (or_outputs[i] == (and_outputs[2*i] | and_outputs[2*i+1]))
        else $error("or_outputs[%0d] mismatch", i);
      cover property (or_outputs[i]);
    end
  endgenerate

  // Mid-level ANDs
  assert property (and_outputs[8] == (or_outputs[0] & or_outputs[1]))
    else $error("and_outputs[8] mismatch");
  assert property (and_outputs[9] == (or_outputs[2] & or_outputs[3]))
    else $error("and_outputs[9] mismatch");
  cover property (and_outputs[8]);
  cover property (and_outputs[9]);

  // Final OR and out
  assert property (or_outputs[4] == (and_outputs[8] | and_outputs[9]))
    else $error("or_outputs[4] mismatch");
  assert property (out == or_outputs[4])
    else $error("out != or_outputs[4]");

  // Golden functional equivalence
  wire gold_left0  = (x[0]&y[0]) | (x[1]&y[1]);
  wire gold_left1  = (x[2]&y[2]) | (x[3]&y[3]);
  wire gold_right0 = (x[4]&y[4]) | (x[5]&y[5]);
  wire gold_right1 = (x[6]&y[6]) | (x[7]&y[7]);
  wire gold = (gold_left0 & gold_left1) | (gold_right0 & gold_right1);

  assert property (out == gold)
    else $error("Functional equivalence failed");

  // No unknowns on outputs when inputs are known
  assert property (!$isunknown(or_outputs[4]) && !$isunknown(out))
    else $error("X/Z on outputs with known inputs");

  // Functional coverage
  cover property (out);
  cover property (!out);
  cover property (and_outputs[8] && !and_outputs[9]); // left tree only
  cover property (!and_outputs[8] && and_outputs[9]); // right tree only
  cover property (and_outputs[8] && and_outputs[9]);  // both trees
endmodule

bind complex complex_sva svacheck();