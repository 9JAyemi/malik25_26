// SVA for sky130_fd_sc_lp__or4
module or4_sva (input logic A, B, C, D, X);

  // Sample on any input/output edge
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C or negedge C or
    posedge D or negedge D or
    posedge X or negedge X
  ); endclocking

  // 4-state functional equivalence
  a_func_eq: assert property (X === (A | B | C | D))
    else $error("OR4 func mismatch: X=%b A=%b B=%b C=%b D=%b", X,A,B,C,D);

  // Deterministic cases: 1-dominance and all-zero
  a_one_dom:  assert property ( (A===1'b1 || B===1'b1 || C===1'b1 || D===1'b1) |-> (X===1'b1) )
    else $error("OR4 1-dominance violated");
  a_all_zero: assert property ( (A===1'b0 && B===1'b0 && C===1'b0 && D===1'b0) |-> (X===1'b0) )
    else $error("OR4 all-zero violated");

  // X/Z propagation when result is otherwise undetermined (no input is 1, at least one is X/Z)
  a_x_prop: assert property (
      !(A===1'b1 || B===1'b1 || C===1'b1 || D===1'b1) &&
      (A!==1'b0 || B!==1'b0 || C!==1'b0 || D!==1'b0)
      |-> X===1'bx
    ) else $error("OR4 X/Z propagation violated");

  // Output 1 implies at least one input 1 (consistency check)
  a_one_cause: assert property ( (X===1'b1) |-> (A===1'b1 || B===1'b1 || C===1'b1 || D===1'b1) )
    else $error("OR4 X=1 without any input=1");

  // Coverage
  c_all_zero:   cover property (A==0 && B==0 && C==0 && D==0 && X==0);
  c_onehot:     cover property ($onehot({A,B,C,D}) && X==1);
  c_multi_one:  cover property (($countones({A,B,C,D}) >= 2) && X==1);
  c_x_propag:   cover property (
                  !(A===1 || B===1 || C===1 || D===1) &&
                  (A!==0 || B!==0 || C!==0 || D!==0) && X===1'bx
                );
  c_x_rise:     cover property (X==0 ##1 X==1);
  c_x_fall:     cover property (X==1 ##1 X==0);

endmodule

// Bind to DUT
bind sky130_fd_sc_lp__or4 or4_sva or4_sva_i (.A(A), .B(B), .C(C), .D(D), .X(X));