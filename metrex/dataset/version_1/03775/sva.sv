// SVA for mult_srst_ena
// Bind into DUT scope so we can check internal ra
module mult_srst_ena_sva;
  default clocking cb @(posedge CLK); endclocking

  // Clean inputs/outputs/state (no X/Z)
  a_inputs_known:  assert property (!$isunknown({RST, ENA, A, B}));
  a_outputs_known: assert property (!$isunknown({ra, Z}));

  // Register behavior
  a_reset_clears_ra:     assert property ($past(RST) |-> ra == 9'd0);
  a_load_on_ena:         assert property ($past(!RST && ENA) |-> ra == $past(A));
  a_hold_when_not_ena:   assert property ($past(!RST && !ENA) |-> ra == $past(ra));

  // Reset dominates ENA
  a_reset_dominates_ena: assert property ($past(RST && ENA) |-> ra == 9'd0);

  // Functional relation: combinational multiply
  a_z_is_product:        assert property (Z == (ra * B));

  // Consequence of ra==0
  a_zero_ra_zero_z:      assert property (ra == 9'd0 |-> Z == 18'd0);

  // Combinational stability: if inputs stable across a cycle, Z stable
  a_stable_inputs_stable_z: assert property ($stable({ra, B}) |-> $stable(Z));

  // Coverage
  c_reset_release:        cover property ($fell(RST));
  c_load_event:           cover property ($past(!RST && ENA) && (ra == $past(A)));
  c_hold_event:           cover property ($past(!RST && !ENA) && (ra == $past(ra)));
  c_reset_and_ena_prio:   cover property (RST && ENA ##1 (ra == 9'd0));
  c_max_inputs:           cover property (ra == {($bits(ra)){1'b1}} && B == {($bits(B)){1'b1}});
endmodule

bind mult_srst_ena mult_srst_ena_sva sva_mult_srst_ena();