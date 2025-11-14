// SVA for: ddr3_s4_uniphy_example_sim_ddr3_s4_uniphy_example_sim_e0_if0_p0_hr_to_fr

bind ddr3_s4_uniphy_example_sim_ddr3_s4_uniphy_example_sim_e0_if0_p0_hr_to_fr
hr_to_fr_sva hr_to_fr_sva_i();

module hr_to_fr_sva;
  // Using DUT scope signals directly via bind
  // past-valid guards (no reset is present)
  bit pos_valid, neg_valid;
  always @(posedge clk) pos_valid <= 1'b1;
  always @(negedge clk) neg_valid <= 1'b1;

  // Posedge capture checks (stage registers update on posedge)
  a_pos_cap_h: assert property (@(posedge clk) disable iff (!pos_valid)
                   (q_h0 == $past(d_h0) && q_h1 == $past(d_h1)));
  a_pos_cap_l: assert property (@(posedge clk) disable iff (!pos_valid)
                   (q_l0 == $past(d_l0) && q_l1 == $past(d_l1)));

  // Negedge capture checks (low-phase shadow regs update on negedge)
  a_neg_cap_lneg: assert property (@(negedge clk) disable iff (!neg_valid)
                         (q_l0_neg == $past(q_l0) && q_l1_neg == $past(q_l1)));

  // Output mux correctness at both phases
  a_mux_hi: assert property (@(posedge clk) (q0 == q_l0_neg && q1 == q_l1_neg));
  a_mux_lo: assert property (@(negedge clk) (q0 == q_h0     && q1 == q_h1));

  // Phase-stability of internal regs
  a_stable_negregs_at_pos: assert property (@(posedge clk) ($stable(q_l0_neg) && $stable(q_l1_neg)));
  a_stable_posregs_at_neg: assert property (@(negedge clk) ($stable(q_h0) && $stable(q_h1) && $stable(q_l0) && $stable(q_l1)));

  // Sanity: outputs are known at edges
  a_no_x_out: assert property (@(posedge clk or negedge clk) (!$isunknown(q0) && !$isunknown(q1)));

  // Coverage: exercise both mux paths and output activity on both edges
  c_mux_hi:  cover property (@(posedge clk) (q0 == q_l0_neg && q1 == q_l1_neg));
  c_mux_lo:  cover property (@(negedge clk) (q0 == q_h0     && q1 == q_h1));
  c_q0_act_pos: cover property (@(posedge clk) (pos_valid && (q0 != $past(q0))));
  c_q0_act_neg: cover property (@(negedge clk) (neg_valid && (q0 != $past(q0))));
  c_q1_act_pos: cover property (@(posedge clk) (pos_valid && (q1 != $past(q1))));
  c_q1_act_neg: cover property (@(negedge clk) (neg_valid && (q1 != $past(q1))));
endmodule