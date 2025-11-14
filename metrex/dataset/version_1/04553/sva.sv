// SVA for module: ascii
// Bind this module to the DUT: bind ascii ascii_sva sva(.dut);
module ascii_sva (ascii dut);

  // State encodings (must match DUT)
  localparam [2:0] st_idle     = 3'b000;
  localparam [2:0] st_code_1   = 3'b001;
  localparam [2:0] st_code_2   = 3'b010;
  localparam [2:0] st_code_3   = 3'b011;
  localparam [2:0] st_break    = 3'b100;
  localparam [2:0] st_extended = 3'b101;
  localparam [2:0] st_ready    = 3'b110;

  default clocking cb @(posedge dut.clk); endclocking

  // Helpers
  let upper = (dut.shift ^ dut.caps_lock);

  // Edge detect correctness
  a_edge_rose_only_when_01: assert property (dut.scan_ready_edge_detect==2'b01 |-> $rose(dut.scan_ready));
  a_edge_01_on_rose:        assert property ($rose(dut.scan_ready) |-> dut.scan_ready_edge_detect==2'b01);

  // FSM sequencing and latching
  a_idle_to_code1:  assert property ((dut.state_reg==st_idle && dut.scan_ready_edge_detect==2'b01)
                                     |=> (dut.state_reg==st_code_1 && dut.current_code==$past(dut.scan_code)));
  a_code1_to_code2: assert property (dut.state_reg==st_code_1 |=> (dut.state_reg==st_code_2 && dut.state_code==$past(dut.current_code)));
  a_code2_branch_b: assert property ((dut.state_reg==st_code_2 && dut.state_code==8'hF0) |=> dut.state_reg==st_break);
  a_code2_branch_m: assert property ((dut.state_reg==st_code_2 && dut.state_code!=8'hF0) |=> dut.state_reg==st_code_3);
  a_code3_to_ready: assert property (dut.state_reg==st_code_3 |=> dut.state_reg==st_ready);
  a_ready_sets_code:assert property (dut.state_reg==st_ready |=> (dut.code==$past(dut.state_code) && dut.state_reg==st_idle));
  a_break_code0:    assert property (dut.state_reg==st_break |=> dut.code==8'h00);
  a_break_edge:     assert property ((dut.state_reg==st_break && dut.scan_ready_edge_detect==2'b01)
                                     |=> (dut.state_reg==st_idle && dut.break_code==$past(dut.scan_code)));
  a_code_stable_else:assert property ((dut.state_reg!=st_ready && dut.state_reg!=st_break) |-> $stable(dut.code));

  // Caps lock behavior
  a_caps_alias:     assert property (dut.caps_lock == dut.caps[0]);
  a_caps_changes_gated: assert property ($changed(dut.caps) |-> (dut.scan_ready_edge_detect==2'b01 && dut.code==8'h58));
  a_caps_inc:       assert property ((dut.scan_ready_edge_detect==2'b01 && dut.code==8'h58) |=> dut.caps==$past(dut.caps)+2'd1);

  // Shift behavior
  a_shift_set:      assert property ((dut.code inside {8'h12,8'h59}) |=> dut.shift==1'b1);
  a_shift_clr:      assert property ((dut.break_code inside {8'h12,8'h59}) |=> dut.shift==1'b0);
  a_shift_changes_gated: assert property ($changed(dut.shift) |-> ((dut.code inside {8'h12,8'h59}) || (dut.break_code inside {8'h12,8'h59})));

  // Extended path never used (as coded)
  a_extended_const0: assert property (dut.extended==1'b0);
  a_never_st_extended: assert property (dut.state_reg!=st_extended);

  // ASCII output consistency
  a_ascii_alias:    assert property (dut.ascii == dut.r_ascii);
  a_ascii_zero_on_code0: assert property (dut.code==8'h00 |-> dut.r_ascii==8'd0);

  // Representative mapping checks (evaluated next cycle due to nonblocking updates)
  a_map_space:  assert property (dut.code==8'h29 |=> dut.r_ascii==8'd32);
  a_map_caps_key_zero: assert property (dut.code==8'h58 |=> dut.r_ascii==8'd0);
  a_map_enter:  assert property (dut.code==8'h5A |=> dut.r_ascii==8'd128);
  a_map_bksp:   assert property (dut.code==8'h66 |=> dut.r_ascii==8'd129);
  // 'A' / 'a'
  a_map_A_uc:   assert property ((dut.code==8'h1C && upper)  |=> dut.r_ascii==8'd65);
  a_map_A_lc:   assert property ((dut.code==8'h1C && !upper) |=> dut.r_ascii==8'd97);
  // '1' / '!'
  a_map_1_sh:   assert property ((dut.code==8'h16 && upper)  |=> dut.r_ascii==8'd33);
  a_map_1_ns:   assert property ((dut.code==8'h16 && !upper) |=> dut.r_ascii==8'd49);

  // Coverage
  c_make_path: cover property (
    dut.state_reg==st_idle && dut.scan_ready_edge_detect==2'b01
    ##1 dut.state_reg==st_code_1
    ##1 (dut.state_reg==st_code_2 && dut.state_code!=8'hF0)
    ##1 dut.state_reg==st_code_3
    ##1 dut.state_reg==st_ready
  );

  c_break_path: cover property (
    dut.state_reg==st_idle && dut.scan_ready_edge_detect==2'b01
    ##1 dut.state_reg==st_code_1
    ##1 (dut.state_reg==st_code_2 && dut.state_code==8'hF0)
    ##1 (dut.state_reg==st_break && dut.scan_ready_edge_detect==2'b01)
  );

  c_caps_toggle: cover property (dut.scan_ready_edge_detect==2'b01 && dut.code==8'h58);
  c_shift_press: cover property (dut.code inside {8'h12,8'h59} ##1 dut.shift==1);
  c_shift_release: cover property (dut.break_code inside {8'h12,8'h59} ##1 dut.shift==0);
  c_alpha_uc: cover property (dut.code==8'h1C && upper ##1 dut.r_ascii==8'd65);
  c_alpha_lc: cover property (dut.code==8'h1C && !upper ##1 dut.r_ascii==8'd97);

endmodule