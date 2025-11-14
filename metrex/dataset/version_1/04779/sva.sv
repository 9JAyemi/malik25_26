// SVA for sky130_fd_sc_lp__and4bb
module sky130_fd_sc_lp__and4bb_sva (
  input logic A_N, B_N, C, D,
  input logic VPWR, VGND, VPB, VNB,
  input logic X
);

  // Sample on any input transition
  default clocking cb @(
    posedge A_N or negedge A_N or
    posedge B_N or negedge B_N or
    posedge C   or negedge C   or
    posedge D   or negedge D   or
    posedge VPWR or negedge VPWR or
    posedge VGND or negedge VGND or
    posedge VPB  or negedge VPB  or
    posedge VNB  or negedge VNB
  ); endclocking

  function automatic logic expected_val;
    expected_val = (~A_N & ~B_N & ~C & ~D & VPWR & VGND & VPB & VNB);
  endfunction

  // Functional equivalence when inputs are known
  assert property ( !$isunknown({A_N,B_N,C,D,VPWR,VGND,VPB,VNB})
                    |-> X === expected_val() )
    else $error("and4bb: X != expected combinational result");

  // Output must be 0/1 when inputs are 0/1
  assert property ( !$isunknown({A_N,B_N,C,D,VPWR,VGND,VPB,VNB})
                    |-> !$isunknown(X) )
    else $error("and4bb: X is X/Z with known inputs");

  // For single or no input change, X must reflect new truth table in same cycle
  assert property ( $onehot0({$changed(A_N),$changed(B_N),$changed(C),$changed(D),
                              $changed(VPWR),$changed(VGND),$changed(VPB),$changed(VNB)})
                    |-> ##0 X === expected_val() )
    else $error("and4bb: combinational settle mismatch on single-input change");

  // X must only change when at least one input changes
  assert property (@(posedge X or negedge X) $changed({A_N,B_N,C,D,VPWR,VGND,VPB,VNB}))
    else $error("and4bb: X changed without any input change");

  // Coverage: reach the 1-minterm and both edges on X
  cover property ( expected_val() && X );
  cover property ( $rose(X) );
  cover property ( $fell(X) );

  // Controllability coverage: each input independently controls X with others enabling
  cover property ( (B_N==1'b0 && C==1'b0 && D==1'b0 && VPWR && VGND && VPB && VNB)
                   ##1 ($stable({B_N,C,D,VPWR,VGND,VPB,VNB}) && $changed(A_N) && $changed(X)) );
  cover property ( (A_N==1'b0 && C==1'b0 && D==1'b0 && VPWR && VGND && VPB && VNB)
                   ##1 ($stable({A_N,C,D,VPWR,VGND,VPB,VNB}) && $changed(B_N) && $changed(X)) );
  cover property ( (A_N==1'b0 && B_N==1'b0 && D==1'b0 && VPWR && VGND && VPB && VNB)
                   ##1 ($stable({A_N,B_N,D,VPWR,VGND,VPB,VNB}) && $changed(C) && $changed(X)) );
  cover property ( (A_N==1'b0 && B_N==1'b0 && C==1'b0 && VPWR && VGND && VPB && VNB)
                   ##1 ($stable({A_N,B_N,C,VPWR,VGND,VPB,VNB}) && $changed(D) && $changed(X)) );
  cover property ( (A_N==1'b0 && B_N==1'b0 && C==1'b0 && D==1'b0 && VGND && VPB && VNB)
                   ##1 ($stable({A_N,B_N,C,D,VGND,VPB,VNB}) && $changed(VPWR) && $changed(X)) );
  cover property ( (A_N==1'b0 && B_N==1'b0 && C==1'b0 && D==1'b0 && VPWR && VPB && VNB)
                   ##1 ($stable({A_N,B_N,C,D,VPWR,VPB,VNB}) && $changed(VGND) && $changed(X)) );
  cover property ( (A_N==1'b0 && B_N==1'b0 && C==1'b0 && D==1'b0 && VPWR && VGND && VNB)
                   ##1 ($stable({A_N,B_N,C,D,VPWR,VGND,VNB}) && $changed(VPB) && $changed(X)) );
  cover property ( (A_N==1'b0 && B_N==1'b0 && C==1'b0 && D==1'b0 && VPWR && VGND && VPB)
                   ##1 ($stable({A_N,B_N,C,D,VPWR,VGND,VPB}) && $changed(VNB) && $changed(X)) );

endmodule

bind sky130_fd_sc_lp__and4bb sky130_fd_sc_lp__and4bb_sva sva_and4bb (.*);