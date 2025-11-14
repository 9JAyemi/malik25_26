// SVA for binary_counter
module binary_counter_sva (binary_counter dut);
  default clocking cb @(posedge dut.CLK); endclocking

  // No X/Z after first sampled cycle
  a_no_x: assert property ($past(1'b1) |-> !$isunknown({dut.RST, dut.Q, dut.Q_reg, dut.Q_next}));

  // Synchronous reset drives Q to zero on the same clock
  a_sync_reset_zero: assert property (dut.RST |-> ##0 (dut.Q == 4'h0));

  // Output wiring correctness
  a_q_matches_reg: assert property (dut.Q == dut.Q_reg);

  // Combinational next-state function correctness
  a_qnext_comb: assert property (dut.Q_next == ((dut.Q_reg == 4'hF) ? 4'h0 : (dut.Q_reg + 4'h1)));

  // Functional next-state: modulo-16 increment when not in reset
  a_count_mod16: assert property ((!dut.RST && $past(1'b1))
                                  |-> dut.Q == (($past(dut.Q) == 4'hF) ? 4'h0 : ($past(dut.Q) + 4'h1)));

  // Pipeline relation: when not in reset, Q equals previous Q_next
  a_q_eq_past_qnext: assert property ((!dut.RST && $past(1'b1)) |-> (dut.Q == $past(dut.Q_next)));

  // Coverage: reset behavior
  c_reset_drives_zero: cover property (dut.RST ##0 (dut.Q == 4'h0));

  // Coverage: full 16-count cycle with wrap (no resets during the cycle)
  c_full_cycle: cover property ((!dut.RST && dut.Q == 4'h0)
                                ##15 (!dut.RST && dut.Q == 4'hF)
                                ##1  (!dut.RST && dut.Q == 4'h0));
endmodule

bind binary_counter binary_counter_sva sva_inst();