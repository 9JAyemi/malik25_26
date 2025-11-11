// SVA for my_module: D flip-flop with complementary output
// Focused, concise checks + essential coverage

module my_module_sva (
  input Q,
  input Q_N,
  input CLK,
  input D
);
  clocking cb @(posedge CLK); endclocking
  default clocking cb;

  // Q captures D on each rising edge (account for initial cycle/unknown past)
  assert property ( !$isunknown($past(D)) |-> (Q === $past(D)) )
    else $error("Q != $past(D) at CLK edge");

  // Q only changes on a CLK rising edge (no mid-cycle glitches)
  assert property ( @(posedge Q or negedge Q) $rose(CLK) )
    else $error("Q changed without CLK rising");

  // Q_N is always the bitwise complement of Q
  assert property ( @(Q or Q_N) !$isunknown({Q,Q_N}) |-> (Q_N === ~Q) )
    else $error("Q_N != ~Q");

  // Q_N updates combinationally with Q (same timestep)
  assert property ( @(posedge Q or negedge Q) ##0 (Q_N === ~Q) )
    else $error("Q_N not immediate complement of Q");

  // If D was known at the previous edge, Q must be known now
  assert property ( !$isunknown($past(D)) |-> !$isunknown(Q) )
    else $error("Q unknown while past D was known");

  // Coverage: observe both Q transitions and both captured values
  cover property ( !$isunknown($past(D)) && (Q === $past(D)) && $rose(Q) );
  cover property ( !$isunknown($past(D)) && (Q === $past(D)) && $fell(Q) );
  cover property ( !$isunknown($past(D)) && (Q === 1'b0) );
  cover property ( !$isunknown($past(D)) && (Q === 1'b1) );
endmodule

bind my_module my_module_sva sva_inst (.*);