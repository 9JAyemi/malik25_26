// SVA for ddr3_s4_uniphy_example_if0_p0_qsys_sequencer_cpu_inst_nios2_oci_fifowp_inc
module fifowp_inc_sva (
  input logic        free2,
  input logic        free3,
  input logic [1:0]  tm_count,
  input logic [3:0]  fifowp_inc
);
  // No X/Z on inputs/outputs
  assert property (!$isunknown({free2,free3,tm_count}));
  assert property (!$isunknown(fifowp_inc));

  // Derived conditions (priority chain)
  let c1 = (free3 && (tm_count == 2'd3));
  let c2 = (free2 && (tm_count >= 2'd2));
  let c3 = (tm_count >= 2'd1);

  // Functional equivalence (concise, covers all cases)
  assert property (fifowp_inc == (c1 ? 4'd3 : c2 ? 4'd2 : c3 ? 4'd1 : 4'd0));

  // Range protection
  assert property (fifowp_inc inside {[4'd0:4'd3]});

  // Optional branch-specific for debug (also confirms priority)
  assert property (c1 |-> (fifowp_inc == 4'd3));
  assert property ((!c1 && c2) |-> (fifowp_inc == 4'd2));
  assert property ((!c1 && !c2 && c3) |-> (fifowp_inc == 4'd1));
  assert property ((!c1 && !c2 && !c3) |-> (fifowp_inc == 4'd0));

  // Coverage: hit each branch and priority overrides at tm_count==3
  cover property (c1 && (fifowp_inc == 4'd3));
  cover property (!c1 && c2 && (fifowp_inc == 4'd2));
  cover property (!c1 && !c2 && c3 && (fifowp_inc == 4'd1));
  cover property (!c1 && !c2 && !c3 && (fifowp_inc == 4'd0));

  cover property (tm_count==2'd3 &&  free3        && (fifowp_inc==4'd3)); // top priority
  cover property (tm_count==2'd3 && !free3 && free2 && (fifowp_inc==4'd2)); // mid priority
  cover property (tm_count==2'd3 && !free3 && !free2 && (fifowp_inc==4'd1)); // fallback
endmodule

bind ddr3_s4_uniphy_example_if0_p0_qsys_sequencer_cpu_inst_nios2_oci_fifowp_inc fifowp_inc_sva sva_i(.*);