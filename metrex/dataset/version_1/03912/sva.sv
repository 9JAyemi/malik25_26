// SVA for DFFSR: synchronous SET with priority over RESET, QN is complement of Q

module DFFSR_sva (input logic CLK, D, SET, RESET, Q, QN);

  default clocking cb @(posedge CLK); endclocking

  // Functional correctness on next clock
  a_set_priority:   assert property (SET               |=> (Q == 1'b1));
  a_reset_no_set:   assert property ((!SET && RESET)   |=> (Q == 1'b0));
  a_data_follow:    assert property ((!SET && !RESET)  |=> (Q == $past(D)));

  // Complement output must always mirror Q (check on both clock phases)
  a_qn_compl_pos:   assert property (@(posedge CLK) (QN === ~Q));
  a_qn_compl_neg:   assert property (@(negedge CLK) (QN === ~Q));

  // Q must not change on negedge (change only allowed at posedge)
  a_no_change_negedge: assert property (@(negedge CLK) $stable(Q));

  // Coverage: exercise all key behaviors
  c_set_wins_over_reset: cover property (SET && RESET         |=> (Q == 1'b1));
  c_reset_only:          cover property (!SET && RESET        |=> (Q == 1'b0));
  c_data_to_one:         cover property (!SET && !RESET && D  |=> (Q == 1'b1));
  c_data_to_zero:        cover property (!SET && !RESET && !D |=> (Q == 1'b0));
  c_data_toggles_up:     cover property (!SET && !RESET && D && !$past(Q) |=> (Q && $past(D)));
  c_data_toggles_down:   cover property (!SET && !RESET && !D &&  $past(Q) |=> (!Q && !$past(D)));

endmodule

// Bind into DUT
bind DFFSR DFFSR_sva dffsr_sva_i (.*);