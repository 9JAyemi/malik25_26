// SVA for sky130_fd_sc_ls__o41ai
// Function: Y = ~(B1 & (A1|A2|A3|A4))

module sky130_fd_sc_ls__o41ai_sva (
  input Y,
  input A1, A2, A3, A4,
  input B1
);
  logic a_or;
  assign a_or = (A1 | A2 | A3 | A4);

  // Use global clock for sampling; replace if your env requires a real clk
  default clocking cb @(posedge $global_clock); endclocking

  // Functional equivalence (golden check)
  assert property (Y === ~(B1 & a_or));

  // No X/Z on output when inputs are known
  assert property (!$isunknown({A1,A2,A3,A4,B1}) |-> !$isunknown(Y));

  // Controlling values / reductions
  assert property (!B1   |-> (Y == 1'b1));     // NAND low input dominates
  assert property (!a_or |-> (Y == 1'b1));     // OR is 0 => NAND output is 1
  assert property ( B1   |-> (Y == ~a_or));    // When B1=1, Y mirrors ~OR

  // Sensitivity to B1 only when OR=1
  assert property (!a_or && $changed(B1) && $stable({A1,A2,A3,A4}) |-> $stable(Y));
  assert property ( a_or && $changed(B1) && $stable({A1,A2,A3,A4}) |-> $changed(Y));

  // Basic functional coverage
  cover property (Y == 1);
  cover property (Y == 0);
  cover property (!B1 && Y == 1);
  cover property ( B1 && !a_or && Y == 1);
  cover property ( B1 &&  a_or && Y == 0);

  // Each Ai alone can force Y low when B1=1
  cover property (B1 &&  A1 && !A2 && !A3 && !A4 && Y == 0);
  cover property (B1 && !A1 &&  A2 && !A3 && !A4 && Y == 0);
  cover property (B1 && !A1 && !A2 &&  A3 && !A4 && Y == 0);
  cover property (B1 && !A1 && !A2 && !A3 &&  A4 && Y == 0);
endmodule

bind sky130_fd_sc_ls__o41ai sky130_fd_sc_ls__o41ai_sva sva_o41ai (.*);