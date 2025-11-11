// SVA for shift_register
// Bind this checker to the DUT type
bind shift_register shift_register_chk u_shift_register_chk (
  .s_axi_aclk      (s_axi_aclk),
  .D               (D),
  .shift_reg_ld0   (shift_reg_ld0),
  .SR              (SR),
  .E               (E),
  .detect_start    (detect_start),
  .detect_stop_reg (detect_stop_reg),
  .sda_sample      (sda_sample),
  .master_slave_reg(master_slave_reg),
  .out             (out),
  .arb_lost_reg    (arb_lost_reg),
  .abgc_i_reg_0    (abgc_i_reg_0),
  .shift_reg_ld    (shift_reg_ld),
  .Q               (Q),
  .shift_reg       (shift_reg)
);

module shift_register_chk (
  input  logic        s_axi_aclk,
  input  logic [7:0]  D,
  input  logic        shift_reg_ld0,
  input  logic        SR,
  input  logic        E,
  input  logic        detect_start,
  input  logic        detect_stop_reg,
  input  logic        sda_sample,
  input  logic        master_slave_reg,
  input  logic [2:0]  out,
  input  logic        arb_lost_reg,
  input  logic        abgc_i_reg_0,
  input  logic        shift_reg_ld,
  input  logic [7:0]  Q,
  input  logic [7:0]  shift_reg
);
  default clocking cb @(posedge s_axi_aclk); endclocking

  // Basic sanity: outputs must never be X/Z
  a_no_x_outputs:  assert (!$isunknown({abgc_i_reg_0, shift_reg_ld, arb_lost_reg, Q}));

  // Q follows prior-cycle shift_reg (due to nonblocking ordering)
  a_q_follows_sr:  assert ($past(1'b1) |-> (Q == $past(shift_reg)));

  // Synchronous reset clears shift_reg and Q by the next cycle
  a_rst_clears_sr: assert (SR |=> (shift_reg == 8'h00));
  a_rst_clears_q:  assert (SR |=> (Q == 8'h00));

  // Hold when E==0 (and not in reset)
  a_hold_when_E0:  assert ($past(1'b1) && !SR && !E |=> shift_reg == $past(shift_reg));

  // Load/clear priority when E==1
  a_clr_on_ld0:    assert (!SR && E &&  shift_reg_ld0                       |=> shift_reg == 8'h00);
  a_clr_on_start:  assert (!SR && E && !shift_reg_ld0 &&  detect_start       |=> shift_reg == 8'h00);

  // Shift left with sda_sample when enabled and no clears
  a_shift:         assert ($past(1'b1) &&
                           !SR && E && !shift_reg_ld0 && !detect_start
                           |=> shift_reg == { $past(shift_reg[6:0]), $past(sda_sample) });

  // Combinational outputs: functional equivalence checks (note truncation to [0])
  // abgc_i_reg_0 = (out==000)?0 : (detect_start?1 : shift_reg[0])
  a_abgc_func:     assert (abgc_i_reg_0 == ((out==3'b000) ? 1'b0
                                             : (detect_start ? 1'b1 : shift_reg[0])));

  // shift_reg_ld branches must produce defined values (no X)
  a_srl_out000:    assert ((out==3'b000) |-> (shift_reg_ld == 1'b0));
  a_srl_out001:    assert ((out==3'b001) |-> (shift_reg_ld == 1'b1));
  a_srl_stop:      assert ((out!=3'b000 && out!=3'b001 && detect_stop_reg) |-> (shift_reg_ld == 1'b1));
  a_srl_ld0:       assert ((out!=3'b000 && out!=3'b001 && !detect_stop_reg && shift_reg_ld0) |-> (shift_reg_ld == 1'b0));
  a_srl_never_x:   assert (!$isunknown(shift_reg_ld));

  // arb_lost_reg functional behavior when master_slave_reg==1
  // If load/start -> 0
  a_arb_zero_on_ld:   assert (master_slave_reg && shift_reg_ld0      |-> arb_lost_reg == 1'b0);
  a_arb_zero_on_strt: assert (master_slave_reg && detect_start       |-> arb_lost_reg == 1'b0);
  // Arbitration lost detect
  a_arb_lost_pulse:   assert (master_slave_reg && !shift_reg_ld0 && !detect_start &&
                               (shift_reg[7]==1'b0) && (sda_sample==1'b1) |-> arb_lost_reg == 1'b1);
  // Otherwise pass-through LSB
  a_arb_else_lsb:     assert (master_slave_reg && !shift_reg_ld0 && !detect_start &&
                               !((shift_reg[7]==1'b0) && (sda_sample==1'b1)) |-> arb_lost_reg == shift_reg[0]);
  a_arb_never_x:      assert (!$isunknown(arb_lost_reg));

  // Coverage: exercise all key behaviors/branches
  c_reset:        cover (SR ##1 (shift_reg==8'h00 && Q==8'h00));
  c_shift:        cover (!SR && E && !shift_reg_ld0 && !detect_start ##1 1);
  c_clr_ld0:      cover (!SR && E && shift_reg_ld0 ##1 (shift_reg==8'h00));
  c_clr_start:    cover (!SR && E && !shift_reg_ld0 && detect_start ##1 (shift_reg==8'h00));
  c_abgc_paths0:  cover (out==3'b000 && abgc_i_reg_0==1'b0);
  c_abgc_paths1:  cover (out!=3'b000 && detect_start && abgc_i_reg_0==1'b1);
  c_abgc_paths2:  cover (out!=3'b000 && !detect_start && abgc_i_reg_0==shift_reg[0]);
  c_srl_0:        cover (out==3'b000 && shift_reg_ld==1'b0);
  c_srl_1a:       cover (out==3'b001 && shift_reg_ld==1'b1);
  c_srl_1b:       cover (out!=3'b000 && out!=3'b001 && detect_stop_reg && shift_reg_ld==1'b1);
  c_arb_hit:      cover (master_slave_reg && !shift_reg_ld0 && !detect_start &&
                         (shift_reg[7]==1'b0) && sda_sample && arb_lost_reg);

endmodule