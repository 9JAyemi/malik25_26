// SVA for shift_register and top_module
// Concise, quality-focused checks and coverage

// Bind to the leaf DUT
module shift_register_sva (shift_register dut);
  default clocking cb @(posedge dut.clk); endclocking

  // Sanity: no X on input at sampling edge; output becomes known after first update
  ap_no_x_d:      assert property ( !$isunknown(dut.d) );
  ap_no_x_q_next: assert property ( 1'b1 |=> !$isunknown(dut.q) );

  // Combinational mirror check (q mirrors internal reg)
  ap_q_mirrors_reg: assert property ( dut.q == dut.shift_reg );

  // Sequential behavior check (as coded, register loads d each cycle due to truncation)
  ap_loads_d: assert property ( 1'b1 |=> (dut.q == $past(dut.d)) );
  ap_reg_loads_d: assert property ( 1'b1 |=> (dut.shift_reg == $past(dut.d)) );

  // Coverage: propagation of a change, and extreme values
  cp_change_propagates: cover property ( $changed(dut.d) ##1 (dut.q == $past(dut.d)) );
  cp_all_zero:          cover property ( dut.d == 8'h00 ##1 dut.q == 8'h00 );
  cp_all_ones:          cover property ( dut.d == 8'hFF ##1 dut.q == 8'hFF );
endmodule
bind shift_register shift_register_sva shift_register_sva_i(.dut);

// Optional: top-level connectivity checks
module top_module_sva (top_module t);
  default clocking cb @(posedge t.clk); endclocking
  ap_conn_clk: assert property ( t.clk === t.sr.clk );
  ap_conn_d:   assert property ( t.d   === t.sr.d   );
  ap_conn_q:   assert property ( t.q   === t.sr.q   );
endmodule
bind top_module top_module_sva top_module_sva_i(.t);