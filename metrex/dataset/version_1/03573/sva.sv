// SVA checker for mux4to1. Sample with any convenient verification clock.
module mux4to1_sva (
  input logic clk,
  input logic rst_n,
  input logic A, B, C, D,
  input logic S0, S1,
  input logic X
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  function automatic bit known2(input logic [1:0] s);
    return !$isunknown(s);
  endfunction

  // Control must be known (prevents unintended latch behavior when S is X/Z)
  a_sel_known:        assert property (known2({S1,S0}));

  // Decode is one-hot when selects are known
  a_decode_onehot:    assert property (known2({S1,S0}) |-> $onehot({~S1 & ~S0, ~S1 &  S0,  S1 & ~S0,  S1 &  S0}));

  // Functional equivalence (zero-cycle combinational behavior, and output known when selected input is known)
  a_func_00:          assert property (known2({S1,S0}) && !S1 && !S0 && !$isunknown(A) |-> ##0 (X == A && !$isunknown(X)));
  a_func_01:          assert property (known2({S1,S0}) && !S1 &&  S0 && !$isunknown(B) |-> ##0 (X == B && !$isunknown(X)));
  a_func_10:          assert property (known2({S1,S0}) &&  S1 && !S0 && !$isunknown(C) |-> ##0 (X == C && !$isunknown(X)));
  a_func_11:          assert property (known2({S1,S0}) &&  S1 &&  S0 && !$isunknown(D) |-> ##0 (X == D && !$isunknown(X)));

  // Any output change must be caused by either a select change or the currently selected data input changing
  a_no_spurious_change: assert property (
    known2({S1,S0}) && $changed(X) |->
         $changed({S1,S0})
      || (!S1 && !S0 && $changed(A))
      || (!S1 &&  S0 && $changed(B))
      || ( S1 && !S0 && $changed(C))
      || ( S1 &&  S0 && $changed(D))
  );

  // Coverage: see all select combinations
  c_sel_00:           cover property (known2({S1,S0}) && !S1 && !S0);
  c_sel_01:           cover property (known2({S1,S0}) && !S1 &&  S0);
  c_sel_10:           cover property (known2({S1,S0}) &&  S1 && !S0);
  c_sel_11:           cover property (known2({S1,S0}) &&  S1 &&  S0);

  // Coverage: both 0/1 propagate for each selection (functional plus data value coverage)
  c_00_out0:          cover property (known2({S1,S0}) && !S1 && !S0 && !$isunknown(A) && X==0);
  c_00_out1:          cover property (known2({S1,S0}) && !S1 && !S0 && !$isunknown(A) && X==1);
  c_01_out0:          cover property (known2({S1,S0}) && !S1 &&  S0 && !$isunknown(B) && X==0);
  c_01_out1:          cover property (known2({S1,S0}) && !S1 &&  S0 && !$isunknown(B) && X==1);
  c_10_out0:          cover property (known2({S1,S0}) &&  S1 && !S0 && !$isunknown(C) && X==0);
  c_10_out1:          cover property (known2({S1,S0}) &&  S1 && !S0 && !$isunknown(C) && X==1);
  c_11_out0:          cover property (known2({S1,S0}) &&  S1 &&  S0 && !$isunknown(D) && X==0);
  c_11_out1:          cover property (known2({S1,S0}) &&  S1 &&  S0 && !$isunknown(D) && X==1);

endmodule

// Example bind (connect clk/rst_n from your TB):
// bind mux4to1 mux4to1_sva u_mux4to1_sva(.clk(tb.clk), .rst_n(tb.rst_n),
//                                         .A(A), .B(B), .C(C), .D(D), .S0(S0), .S1(S1), .X(X));