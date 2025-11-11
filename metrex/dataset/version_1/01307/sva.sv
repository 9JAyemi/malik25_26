// SVA for top_module
module top_module_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  logic past_valid;
  always_ff @(posedge clk) begin
    if (reset) past_valid <= 1'b0; else past_valid <= 1'b1;
  end

  // Output wiring
  a_out_mux: assert property (toggled == toggled_reg && count == count_reg && final_output == final_output_reg);

  // Toggling pipeline
  a_dff_in:      assert property (past_valid |-> dff_in      == $past(in));
  a_dff_out:     assert property (past_valid |-> dff_out     == $past(dff_in ^ toggled_reg));
  a_toggled_reg: assert property (past_valid |-> toggled_reg == $past(dff_out));

  // Popcount correctness and range
  a_count_correct: assert property (count_wire == $countones(in));
  a_count_reg:     assert property (past_valid |-> count_reg == $past(count_wire));
  a_count_range:   assert property (count_wire <= 8 && count_reg <= 8);

  // Final output pipeline (truncated sum)
  a_final_reg: assert property (past_valid |-> final_output_reg == ($past(toggled_reg) + $past(count_reg))[7:0]);

  // XOR comb path must exist and match intended function
  a_xor_defined:           assert property (!$isunknown(xor_out) && xor_out == (dff_in ^ toggled_reg));
  a_toggled_wire_consistent: assert property (toggled_wire == xor_out);

  // No X on key outputs once out of reset
  a_no_x_outputs: assert property (past_valid |-> !$isunknown({toggled, count, final_output}));

  // Coverage
  c_popcount_zero:    cover property (count_wire == 0);
  c_popcount_full:    cover property (count_wire == 8);
  c_toggle_activity:  cover property (past_valid && toggled != $past(toggled));
  c_final_overflow:   cover property (past_valid && ({1'b0,$past(toggled_reg)} + {1'b0,$past(count_reg)})[8]);
endmodule

bind top_module top_module_sva sva_inst();