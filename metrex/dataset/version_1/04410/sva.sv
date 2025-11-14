// Bind these SVA into the DUT scope
bind mux_parity mux_parity_sva mp_sva();

module mux_parity_sva;

  // These assertions are clockless and use ##0 to check after combinational settle

  // MUX correctness (integration): mux_out must equal a/b per sel_b1
  property p_mux_sel;
    (!$isunknown({a,b,sel_b1})) |-> ##0 (mux_out == (sel_b1 ? b : a));
  endproperty
  assert property (p_mux_sel) else $error("mux_out != selected input");

  // Output wiring: lower 8 bits and parity bit must match internal wires
  property p_out_wiring;
    (!$isunknown({mux_out,parity})) |-> ##0 (out[7:0] == mux_out && out[8] == parity);
  endproperty
  assert property (p_out_wiring) else $error("out wiring mismatch");

  // Parity generator correctness
  property p_parity_correct;
    (!$isunknown(mux_out)) |-> ##0 (parity == ^mux_out);
  endproperty
  assert property (p_parity_correct) else $error("parity != XOR(mux_out)");

  // Top-level parity consistency (redundant cross-check)
  property p_top_parity_consistent;
    (!$isunknown(out[7:0])) |-> ##0 (out[8] == ^out[7:0]);
  endproperty
  assert property (p_top_parity_consistent) else $error("out[8] != XOR(out[7:0])");

  // Select must be known (helps catch uninitialized control)
  assert property (!$isunknown(sel_b1)) else $error("sel_b1 is X/Z");

  // When inputs and sel_b1 are known, out must be fully known next delta
  property p_known_inputs_produce_known_out;
    (!$isunknown({a,b,sel_b1})) |-> ##0 !$isunknown(out);
  endproperty
  assert property (p_known_inputs_produce_known_out) else $error("out has X/Z with known inputs");

  // Prove sel_b2 has no effect on the design (unused control)
  property p_sel_b2_no_effect;
    $stable(a) && $stable(b) && $stable(sel_b1) && !$stable(sel_b2) |-> ##0 $stable(out);
  endproperty
  assert property (p_sel_b2_no_effect) else $error("sel_b2 unexpectedly affects out");

  // Functional coverage
  cover property (sel_b1 == 1'b0 && out[7:0] == a);
  cover property (sel_b1 == 1'b1 && out[7:0] == b);
  cover property (out[8] == 1'b0);
  cover property (out[8] == 1'b1);
  // Exercise select switch and see corresponding mux output
  cover property (!$isunknown({a,b}) && $changed(sel_b1) ##0 (out[7:0] == (sel_b1 ? b : a)));
  // Observe sel_b2 toggling (to exercise the "no effect" assertion)
  cover property ($changed(sel_b2));

endmodule