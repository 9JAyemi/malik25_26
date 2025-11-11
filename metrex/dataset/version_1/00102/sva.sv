// SVA for memory_controller
// Bind this file to the DUT:
//   bind memory_controller mc_sva mc_sva_i();

module mc_sva;

  // Access DUT scope (names resolved in bound instance)
  default clocking cb @(posedge clock); endclocking
  default disable iff (!reset_b);

  // Helper for safe $past usage
  logic past_valid;
  always_ff @(posedge clock or negedge reset_b) begin
    if (!reset_b) past_valid <= 1'b0;
    else          past_valid <= 1'b1;
  end

  // Structural/comb logic equivalence
  a_cs_mirror:         assert property (ram_cs_b == ext_cs_b);
  a_addr_map:          assert property (ram_addr == {cpu_addr[16:0], ext_a_lsb});
  a_ext_lsb_is_count:  assert property (ext_a_lsb == count);

  // Registered behavior
  a_count_update:      assert property (past_valid |-> (count == !$past(ext_cs_b)));

  // cpu_clken must be 1 when CS inactive
  a_clken_idle:        assert property (ext_cs_b |-> cpu_clken);

  // cpu_clken exactly one-cycle low at CS assertion, then high while CS remains low
  a_clken_on_fall:     assert property ($fell(ext_cs_b) |-> (cpu_clken==0 && count==0));
  a_clken_after_first: assert property (past_valid && (ext_cs_b==0 && $past(ext_cs_b)==0) |-> (cpu_clken==1 && count==1));

  // Read/Write enables and mutual exclusivity
  a_oe_logic:          assert property (ram_oe_b   == !cpu_rnw);
  a_data_oe_logic:     assert property (ram_data_oe== !cpu_rnw);
  a_no_oe_and_we_pos:  assert property (!(ram_oe_b==1'b0 && ram_we_b==1'b0));

  // WE timing vs clock phase
  a_we_posedge:        assert property (ram_we_b == (ext_cs_b | cpu_rnw));
  a_we_negedge:        assert property (@(negedge clock) disable iff(!reset_b) ram_we_b==1'b1);

  // Data path checks
  a_data_out_sel:      assert property (ram_data_out == (ext_a_lsb ? cpu_dout[31:16] : cpu_dout[15:0]));
  a_ext_dout_concat:   assert property (past_valid |-> (ext_dout == {ram_data_in, $past(ram_data_in)}));

  // No-X on primary outputs in active mode
  a_known_outputs:     assert property (!$isunknown({cpu_clken, ram_cs_b, ram_oe_b, ram_we_b, ram_addr, ram_data_oe, ram_data_out, ext_dout})));

  // Safety: never assert OE and WE low at the same time (both edges)
  a_no_oe_and_we_neg:  assert property (@(negedge clock) disable iff(!reset_b) !(ram_oe_b==1'b0 && ram_we_b==1'b0));

  // Coverage
  c_read_2cyc:         cover property ($fell(ext_cs_b) && cpu_rnw ##1 (ext_cs_b==0) ##1 (ext_cs_b==0));
  c_write_pulse:       cover property ($fell(ext_cs_b) && !cpu_rnw ##1 (ram_we_b==1'b0) ##1 $rose(ext_cs_b));
  c_b2b:               cover property ($fell(ext_cs_b) ##[1:5] $rose(ext_cs_b) ##[1:5] $fell(ext_cs_b));
  c_count_rise:        cover property ($rose(count));
  c_half_selects:      cover property (ext_a_lsb==1'b0 ##1 ext_a_lsb==1'b1);

endmodule

bind memory_controller mc_sva mc_sva_i();