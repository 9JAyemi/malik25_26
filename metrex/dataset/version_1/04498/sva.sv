// SVA checker for mux_2to1
module mux_2to1_sva(input logic A0, A1, S, X);

  // Sample on any relevant signal edge
  default clocking cb @(posedge A0 or negedge A0
                       or posedge A1 or negedge A1
                       or posedge S  or negedge S
                       or posedge X  or negedge X); endclocking

  // Functional equivalence (race-safe with ##0)
  a_func: assert property (1'b1 |-> ##0 (X === (S ? A1 : A0)));

  // Propagation from selected input (zero-latency)
  a_prop0: assert property (@(posedge A0 or negedge A0) (S==1'b0) |-> ##0 (X === A0));
  a_prop1: assert property (@(posedge A1 or negedge A1) (S==1'b1) |-> ##0 (X === A1));

  // Non-interference from deselected input
  a_nonint1: assert property (@(posedge A1 or negedge A1) (S==1'b0) |-> ##0 (X == $past(X)));
  a_nonint0: assert property (@(posedge A0 or negedge A0) (S==1'b1) |-> ##0 (X == $past(X)));

  // Select changes pick correct input
  a_s_lo: assert property (@(negedge S) ##0 (X === A0));
  a_s_hi: assert property (@(posedge S) ##0 (X === A1));

  // X changes only if S or the selected input changes
  a_glitchfree: assert property (@(posedge X or negedge X)
                    ($changed(S)) ||
                    ((S==1'b0) && $changed(A0)) ||
                    ((S==1'b1) && $changed(A1)));

  // No X/Z on interface
  a_no_xz: assert property (1'b1 |-> ##0 (!$isunknown({A0,A1,S,X})));

  // Coverage
  c_sel0:  cover property (1'b1 |-> ##0 (S==1'b0 && X===A0));
  c_sel1:  cover property (1'b1 |-> ##0 (S==1'b1 && X===A1));
  c_sneg:  cover property (@(negedge S) ##0 (X===A0));
  c_spos:  cover property (@(posedge S) ##0 (X===A1));
  c_a0sel: cover property (@(posedge A0 or negedge A0) (S==1'b0) |-> ##0 (X===A0));
  c_a1sel: cover property (@(posedge A1 or negedge A1) (S==1'b1) |-> ##0 (X===A1));

  // Hit all (S,A0,A1,X) combinations consistent with spec
  c_0000: cover property (1'b1 |-> ##0 (S==0 && A0==0 && A1==0 && X==0));
  c_0010: cover property (1'b1 |-> ##0 (S==0 && A0==0 && A1==1 && X==0));
  c_0111: cover property (1'b1 |-> ##0 (S==0 && A0==1 && A1==1 && X==1));
  c_0101: cover property (1'b1 |-> ##0 (S==0 && A0==1 && A1==0 && X==1));
  c_1000: cover property (1'b1 |-> ##0 (S==1 && A0==0 && A1==0 && X==0));
  c_1011: cover property (1'b1 |-> ##0 (S==1 && A0==0 && A1==1 && X==1));
  c_1100: cover property (1'b1 |-> ##0 (S==1 && A0==1 && A1==0 && X==0));
  c_1111: cover property (1'b1 |-> ##0 (S==1 && A0==1 && A1==1 && X==1));

endmodule

// Bind into the DUT
bind mux_2to1 mux_2to1_sva u_mux_2to1_sva (.A0(A0), .A1(A1), .S(S), .X(X));