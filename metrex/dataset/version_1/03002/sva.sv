// SVA for sky130_fd_sc_lp__a21o: X = (A1 & A2) | B1

module a21o_sva;
  // Sample on any relevant edge
  default clocking cb @(posedge A1 or negedge A1
                      or posedge A2 or negedge A2
                      or posedge B1 or negedge B1
                      or posedge X  or negedge X); endclocking

  // Functional correctness
  assert property (disable iff ($isunknown({A1,A2,B1}))
                   X == ((A1 & A2) | B1));

  // Internal cone equivalence
  assert property (disable iff ($isunknown({A1,A2}))
                   and0_out == (A1 & A2));
  assert property (disable iff ($isunknown({and0_out,B1}))
                   or0_out_X == (and0_out | B1));
  assert property (disable iff ($isunknown(or0_out_X))
                   X == or0_out_X);

  // No X/Z on output when inputs are known
  assert property (disable iff ($isunknown({A1,A2,B1}))
                   !$isunknown(X));

  // Functional coverage: all 8 input combinations and expected X
  cover property (B1==1 && A1==0 && A2==0 && X==1);
  cover property (B1==1 && A1==0 && A2==1 && X==1);
  cover property (B1==1 && A1==1 && A2==0 && X==1);
  cover property (B1==1 && A1==1 && A2==1 && X==1);

  cover property (B1==0 && A1==0 && A2==0 && X==0);
  cover property (B1==0 && A1==0 && A2==1 && X==0);
  cover property (B1==0 && A1==1 && A2==0 && X==0);
  cover property (B1==0 && A1==1 && A2==1 && X==1);
endmodule

bind sky130_fd_sc_lp__a21o a21o_sva a21o_sva_i();