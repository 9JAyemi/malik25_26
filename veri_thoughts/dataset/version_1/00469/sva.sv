// SVA for johnson_counter
module johnson_counter_sva (
  input  logic        clk,
  input  logic [3:0]  Q,
  input  logic [3:0]  shift_reg
);
  default clocking cb @(posedge clk); endclocking

  // Shift/rotate behavior
  ap_rotate: assert property ( !$isunknown($past(shift_reg))
                               |-> shift_reg == {$past(shift_reg[2:0]), $past(shift_reg[3])} );

  // Q mapping (from prior shift_reg)
  ap_q_from_past_sr: assert property ( !$isunknown($past(shift_reg))
                                       |-> Q == {3'b000, ($past(shift_reg[0]) ^ $past(shift_reg[3]))} );

  // Q invariant w.r.t. current shift_reg (after one update)
  ap_q_invariant: assert property ( !$isunknown(shift_reg)
                                    |-> Q == {3'b000, (shift_reg[1] ^ shift_reg[0])} );

  // No glitches between clock edges (registered signals)
  ap_stable_between_edges: assert property (@(negedge clk) $stable(Q) && $stable(shift_reg));

  // Coverage
  cp_q0_0_then_1: cover property (Q[0]==0 ##1 Q[0]==1);
  cp_q0_1_then_0: cover property (Q[0]==1 ##1 Q[0]==0);
  cp_sr_changes:  cover property ($changed(shift_reg));
endmodule

bind johnson_counter johnson_counter_sva u_sva (.*);