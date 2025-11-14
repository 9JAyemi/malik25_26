// SVA for barrel_shifter_16bit
// Bind into DUT scope so internal regs are visible
module barrel_shifter_16bit_sva;

  // Event-based sampling for combinational DUT
  event comb_ev; always @* -> comb_ev;
  default clocking cb @(comb_ev); endclocking

  // Reference model (even shifts only)
  let eff_shift = {shift_amount[3], shift_amount[2], shift_amount[1], 1'b0};
  let ref_stage1 = (shift_amount[3]) ? (data << 8) : data;
  let ref_stage2 = (shift_amount[2]) ? (ref_stage1 << 4) : ref_stage1;
  let ref_out    = (shift_amount[1]) ? (ref_stage2 << 2) : ref_stage2;

  // Functional correctness (guard unknowns)
  assert property (disable iff ($isunknown({data, shift_amount[3:1]}))
                   out == (data << eff_shift));
  // Pipeline stage equivalence
  assert property (disable iff ($isunknown({data, shift_amount[3]}))
                   stage1_out == ref_stage1);
  assert property (disable iff ($isunknown({ref_stage1, shift_amount[2]}))
                   stage2_out == ref_stage2);
  assert property (disable iff ($isunknown({ref_stage2, shift_amount[1]}))
                   out == ref_out);

  // Zero-fill guarantees for each controlled shift stage
  assert property (disable iff ($isunknown(shift_amount[1]))
                   shift_amount[1] |-> (out[1:0] == 2'b00));
  assert property (disable iff ($isunknown(shift_amount[2]))
                   shift_amount[2] |-> (out[3:0] == 4'b0000));
  assert property (disable iff ($isunknown(shift_amount[3]))
                   shift_amount[3] |-> (out[7:0] == 8'h00));

  // Output stability when inputs that matter are stable
  assert property ($stable({data, shift_amount[3:1]})) |-> $stable({stage1_out, stage2_out, out});

  // Unused LSB of shift_amount must not affect outputs (when others stable)
  assert property (@(posedge shift_amount[0] or negedge shift_amount[0])
                   $stable({data, shift_amount[3:1]})) |-> $stable({stage1_out, stage2_out, out});

  // Basic X-checks on control and outputs when inputs known
  assert property (!$isunknown(shift_amount[3:1]));
  assert property ((!$isunknown({data, shift_amount[3:1]})) |-> (!$isunknown({stage1_out, stage2_out, out})));

  // Coverage: exercise all effective shift amounts implemented (0,2,...,14)
  cover property (eff_shift == 4'd0);
  cover property (eff_shift == 4'd2);
  cover property (eff_shift == 4'd4);
  cover property (eff_shift == 4'd6);
  cover property (eff_shift == 4'd8);
  cover property (eff_shift == 4'd10);
  cover property (eff_shift == 4'd12);
  cover property (eff_shift == 4'd14);

  // Coverage: demonstrate shift_amount[0] toggles without affecting outputs
  cover property (@(posedge shift_amount[0]) $stable({data, shift_amount[3:1]}));
  cover property (@(negedge shift_amount[0]) $stable({data, shift_amount[3:1]}));

endmodule

bind barrel_shifter_16bit barrel_shifter_16bit_sva bs16_sva();