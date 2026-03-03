// SVA for my_module: checks functionality, power pins, X-propagation, and basic coverage.
// Bind this file to the DUT:  bind my_module my_module_sva sva_my_module();

module my_module_sva;

  // Trigger on any relevant change (combinational block)
  default clocking cb @ (A1 or A2 or A3 or B1 or X or and0_out or or0_out_X or VPWR or VGND or VPB or VNB);
  endclocking

  // Helpers
  let pg_ok        = (VPWR === 1'b1 && VGND === 1'b0);
  let rails_tied   = (VPB === VPWR) && (VNB === VGND);
  let power_good   = pg_ok && rails_tied;
  let inputs_known = !$isunknown({A1, A2, A3, B1});

  // Power integrity
  a_rails_tied:        assert property (rails_tied)
                        else $error("VPB/VNB not tied to VPWR/VGND");
  a_power_levels:      assert property (pg_ok)
                        else $error("VPWR/VGND not at legal levels 1/0");

  // No X/Z on functional inputs under power_good
  a_no_x_inputs:       assert property (power_good |-> inputs_known)
                        else $error("Inputs contain X/Z under power_good");

  // Internal cone correctness
  a_and_correct:       assert property (power_good && !$isunknown({A1,A2,A3})
                                        |-> and0_out === (A1 & A2 & A3))
                        else $error("and0_out mismatch");
  a_or_correct:        assert property (power_good && !$isunknown({and0_out,B1})
                                        |-> or0_out_X === (and0_out | B1))
                        else $error("or0_out_X mismatch");
  a_buf_correct:       assert property (power_good && !$isunknown(or0_out_X)
                                        |-> X === or0_out_X)
                        else $error("Buffer X mismatch");

  // End-to-end Boolean equivalence and X-propagation check
  a_end_to_end:        assert property (power_good && inputs_known
                                        |-> X === ((A1 & A2 & A3) | B1))
                        else $error("X != (A1&A2&A3)|B1 under power_good");
  a_xprop_out:         assert property (power_good && inputs_known
                                        |-> !$isunknown(X))
                        else $error("X is X/Z with known inputs under power_good");

  // Minimal functional coverage
  c_power_good:        cover property (power_good);
  c_b1_drives_high:    cover property (power_good && B1 && X);
  c_and_drives_high:   cover property (power_good && !B1 && A1 && A2 && A3 && X);
  c_drives_low:        cover property (power_good && !(B1 || (A1 && A2 && A3)) && !X);

  // Toggle coverage (inputs and output)
  c_a1_rise:           cover property (power_good && $rose(A1));
  c_a1_fall:           cover property (power_good && $fell(A1));
  c_a2_rise:           cover property (power_good && $rose(A2));
  c_a2_fall:           cover property (power_good && $fell(A2));
  c_a3_rise:           cover property (power_good && $rose(A3));
  c_a3_fall:           cover property (power_good && $fell(A3));
  c_b1_rise:           cover property (power_good && $rose(B1));
  c_b1_fall:           cover property (power_good && $fell(B1));
  c_x_rise:            cover property (power_good && $rose(X));
  c_x_fall:            cover property (power_good && $fell(X));

endmodule