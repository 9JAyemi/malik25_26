// SVA for and4b: concise, high-quality checks + coverage
// Bind into DUT to access internal nets

module and4b_sva
(
  input logic A_N, B, C, D, X,
  input logic not0_out, and0_out, and1_out,
  input logic VPWR, VPB, VGND, VNB
);

  // Sample on any relevant combinational change
  default clocking cb @(A_N or B or C or D or not0_out or and0_out or and1_out or X); endclocking

  // Functional equivalence (primary check)
  assert property (X === ((~A_N) & B & C & D))
    else $error("and4b func mismatch: X != (~A_N & B & C & D)");

  // Internal gate-level consistency
  assert property (not0_out === ~A_N)
    else $error("and4b inv mismatch: not0_out != ~A_N");
  assert property (and0_out === (B & C))
    else $error("and4b and0 mismatch: and0_out != (B & C)");
  assert property (and1_out === (not0_out & D & and0_out))
    else $error("and4b and1 mismatch: and1_out != (not0_out & D & and0_out)");
  assert property (X === and1_out)
    else $error("and4b buf mismatch: X != and1_out");

  // X-propagation: known inputs produce known internal nets/output
  assert property (!$isunknown({A_N,B,C,D}) |-> !$isunknown({not0_out,and0_out,and1_out,X}))
    else $error("and4b X-prop: known inputs produced X/Z internally or at output");

  // Supplies sanity (should be constant rails)
  initial begin
    assert (VPWR === 1'b1 && VPB === 1'b1 && VGND === 1'b0 && VNB === 1'b0)
      else $error("and4b supplies incorrect");
  end

  // Minimal but meaningful coverage
  cover property (X);         // observe high
  cover property (!X);        // observe low
  cover property ($rose(X));  // X rises
  cover property ($fell(X));  // X falls

  // Full input combination coverage (16 combos) via compact covergroup
  covergroup cg_inputs with function sample(bit a, bit b, bit c, bit d);
    cp_a: coverpoint a;
    cp_b: coverpoint b;
    cp_c: coverpoint c;
    cp_d: coverpoint d;
    all_x: cross cp_a, cp_b, cp_c, cp_d;
  endgroup
  cg_inputs cg = new;
  always @* if (!$isunknown({A_N,B,C,D})) cg.sample(A_N,B,C,D);

endmodule

bind and4b and4b_sva u_and4b_sva(.*);