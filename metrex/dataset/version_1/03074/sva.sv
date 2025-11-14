// SVA for sky130_fd_sc_lp__nand2
// Bindable, concise, and covers functional, X/Z, and toggle behavior

module sky130_fd_sc_lp__nand2_sva (input logic A, B, Y);
  // Clockless concurrent assertions: sample on any edge of A, B, or Y
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge Y or negedge Y
  ); endclocking

  // 2-state functional correctness
  assert property ( (! $isunknown(A) && ! $isunknown(B)) |-> ##0 (Y === ~(A & B)) )
    else $error("NAND2 func mismatch: A=%b B=%b Y=%b", A, B, Y);

  // Forcing cases with 4-state semantics
  assert property ( (A === 1'b0 || B === 1'b0) |-> ##0 (Y === 1'b1) )
    else $error("NAND2 forcing-1 violated: A=%b B=%b Y=%b", A, B, Y);

  assert property ( (A === 1'b1 && B === 1'b1) |-> ##0 (Y === 1'b0) )
    else $error("NAND2 both-1 violated: A=%b B=%b Y=%b", A, B, Y);

  // X-propagation when no known-0 present
  assert property ( (($isunknown(A) || $isunknown(B)) && !(A===1'b0 || B===1'b0)) |-> ##0 $isunknown(Y) )
    else $error("NAND2 X-prop violated: A=%b B=%b Y=%b", A, B, Y);

  // Output is never Z (driven cell)
  assert property ( 1'b1 |-> ##0 (Y !== 1'bz) )
    else $error("NAND2 Y is Z");

  // No spurious output toggle without input activity
  assert property ( $changed(Y) |-> !$stable({A,B}) )
    else $error("NAND2 Y toggled without A/B change");

  // Coverage: all 2-state input combos and both Y edges, plus X-prop
  cover property (A===1'b0 && B===1'b0 && Y===1'b1);
  cover property (A===1'b0 && B===1'b1 && Y===1'b1);
  cover property (A===1'b1 && B===1'b0 && Y===1'b1);
  cover property (A===1'b1 && B===1'b1 && Y===1'b0);
  cover property ($rose(Y));
  cover property ($fell(Y));
  cover property (($isunknown(A) || $isunknown(B)) && !(A===1'b0 || B===1'b0) && $isunknown(Y));
endmodule

bind sky130_fd_sc_lp__nand2 sky130_fd_sc_lp__nand2_sva u_nand2_sva (.A(A), .B(B), .Y(Y));