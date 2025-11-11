// SVA for pg_5
module pg_5_sva (pg_5 dut);
  default clocking cb @(*); endclocking

  wire inputs_known = !$isunknown({dut.g, dut.p, dut.g_prec, dut.p_prec});

  // Functional correctness (with X-safety)
  ap_func: assert property (
    inputs_known |-> (
      dut.p_out == (dut.p & dut.p_prec) &&
      dut.g_out == (dut.g | (dut.p & dut.g_prec)) &&
      !$isunknown({dut.p_out, dut.g_out})
    )
  );

  // Internal nets sanity
  ap_n6: assert property (inputs_known |-> dut.n6 == ~dut.g);
  ap_n5: assert property (inputs_known |-> dut.n5 == ~(dut.p & dut.g_prec));

  // Dominance/propagate checks
  ap_g_dominates: assert property ((inputs_known && dut.g) |-> dut.g_out);
  ap_prop_path:   assert property ((inputs_known && !dut.g && dut.p && dut.g_prec) |-> dut.g_out);

  // Coverage: key scenarios and both output polarities
  cp_direct_generate:     cover property (inputs_known && dut.g && dut.g_out);
  cp_propagate_generate:  cover property (inputs_known && !dut.g && dut.p && dut.g_prec && dut.g_out);
  cp_kill:                cover property (inputs_known && !dut.g && !(dut.p && dut.g_prec) && !dut.g_out);
  cp_p_chain_on:          cover property (inputs_known && dut.p && dut.p_prec && dut.p_out);
  cp_gout0:               cover property (inputs_known && !dut.g_out);
  cp_gout1:               cover property (inputs_known &&  dut.g_out);
  cp_pout0:               cover property (inputs_known && !dut.p_out);
  cp_pout1:               cover property (inputs_known &&  dut.p_out);
endmodule

bind pg_5 pg_5_sva u_pg_5_sva(.dut());