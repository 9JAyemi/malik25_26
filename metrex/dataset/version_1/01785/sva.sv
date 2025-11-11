// SVA checker for two_input_logic
module two_input_logic_sva (
  input logic A,
  input logic B,
  input logic X,
  input logic not_A,
  input logic not_B,
  input logic and1_out,
  input logic and2_out,
  input logic or_out
);

  // Steady-state functional equivalence (immediate assertions)
  always_comb begin
    assert (not_A   === ~A)                         else $error("not_A != ~A");
    assert (not_B   === ~B)                         else $error("not_B != ~B");
    assert (and1_out=== (A & ~B))                   else $error("and1_out != (A & ~B)");
    assert (and2_out=== (~A & B))                   else $error("and2_out != (~A & B)");
    assert (or_out  === (and1_out | and2_out))      else $error("or_out != and1|and2");
    assert (or_out  === (A ^ B))                    else $error("or_out != A^B");
    assert (X       === ~or_out)                    else $error("X != ~or_out");
    assert (X       === (A ~^ B))                   else $error("X != A~^B (XNOR)");
    // Mutually exclusive partial products
    assert (!(and1_out && and2_out))                else $error("and1_out && and2_out both 1");
  end

  // Inputs must be known when they change; known inputs produce known outputs
  assert property (@(A or B) !$isunknown({A,B}))
    else $error("A/B unknown (X/Z)");
  assert property (@(A or B) (!$isunknown({A,B}) |-> !$isunknown({X,not_A,not_B,and1_out,and2_out,or_out})))
    else $error("Output/ints unknown with known inputs");

  // Functional coverage: all input/output truth-table points
  cover property (@(A or B) (A==0 && B==0 && X==1));
  cover property (@(A or B) (A==0 && B==1 && X==0));
  cover property (@(A or B) (A==1 && B==0 && X==0));
  cover property (@(A or B) (A==1 && B==1 && X==1));

  // Coverage: each internal term activates; all edges seen
  cover property (@(A or B) and1_out);
  cover property (@(A or B) and2_out);
  cover property (@(posedge A));
  cover property (@(negedge A));
  cover property (@(posedge B));
  cover property (@(negedge B));
  cover property (@(posedge X));
  cover property (@(negedge X));

endmodule

// Bind into the DUT to access internal nets
bind two_input_logic two_input_logic_sva u_two_input_logic_sva (.*);