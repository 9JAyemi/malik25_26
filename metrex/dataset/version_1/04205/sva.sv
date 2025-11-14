// SVA for controllerPeripheralHdlAdi_tc
module controllerPeripheralHdlAdi_tc_sva
(
  input logic        CLK_IN,
  input logic        reset,
  input logic        clk_enable,
  input logic        enb,
  input logic        enb_1_1_1,
  input logic        enb_1_2000_0,
  input logic        enb_1_2000_1,
  input logic [10:0] count2000,
  input logic        phase_all,
  input logic        phase_0,
  input logic        phase_1
);

  default clocking cb @(posedge CLK_IN); endclocking
  default disable iff (reset);

  // Basic equivalences and ranges
  a_phase_all_eq:    assert property (phase_all == clk_enable);
  a_enb_eq:          assert property (enb == clk_enable);
  a_enb111_eq:       assert property (enb_1_1_1 == clk_enable);
  a_count_range:     assert property (count2000 <= 11'd1999);

  // Synchronous reset effect (one cycle later)
  a_reset_vals:      assert property (reset |=> (count2000==11'd1 && phase_0==1'b0 && phase_1==1'b1));

  // Hold when not enabled
  a_hold_when_gated: assert property (!clk_enable |-> $stable({count2000,phase_0,phase_1}));

  // Counter next-state when enabled
  a_cnt_inc:         assert property ($past(clk_enable) && $past(count2000)!=11'd1999 |-> count2000 == $past(count2000)+11'd1);
  a_cnt_wrap:        assert property ($past(clk_enable) && $past(count2000)==11'd1999 |-> count2000 == 11'd0);

  // Phase generation correctness
  a_phase0_from_cnt: assert property (phase_0 |-> ($past(clk_enable) && $past(count2000)==11'd1999));
  a_phase1_from_cnt: assert property (phase_1 |-> ($past(clk_enable) && $past(count2000)==11'd0));
  a_cnt_to_phase0:   assert property ($past(clk_enable) && $past(count2000)==11'd1999 |-> phase_0);
  a_cnt_to_phase1:   assert property ($past(clk_enable) && $past(count2000)==11'd0    |-> phase_1);

  // Output pulses vs count (require consecutive enable)
  a_enb2000_0_bi:    assert property (enb_1_2000_0 <-> (clk_enable && $past(clk_enable) && $past(count2000)==11'd1999));
  a_enb2000_1_bi:    assert property (enb_1_2000_1 <-> (clk_enable && $past(clk_enable) && $past(count2000)==11'd0));

  // Mutual exclusivity of 2000-rate enables
  a_mut_excl:        assert property (!(enb_1_2000_0 && enb_1_2000_1));

  // No X on key signals (outside reset)
  a_no_x:            assert property (!$isunknown({clk_enable,enb,enb_1_1_1,enb_1_2000_0,enb_1_2000_1,count2000,phase_0,phase_1}));

  // Coverage
  c_reset_release:   cover  property (reset ##1 !reset);
  c_wrap_pulse:      cover  property ($past(clk_enable) && $past(count2000)==11'd1999 ##1 (clk_enable && enb_1_2000_0) ##1 (clk_enable && enb_1_2000_1));
endmodule

// Bind into DUT (connects to internal regs/wires)
bind controllerPeripheralHdlAdi_tc controllerPeripheralHdlAdi_tc_sva
  sva_i( .CLK_IN(CLK_IN),
         .reset(reset),
         .clk_enable(clk_enable),
         .enb(enb),
         .enb_1_1_1(enb_1_1_1),
         .enb_1_2000_0(enb_1_2000_0),
         .enb_1_2000_1(enb_1_2000_1),
         .count2000(count2000),
         .phase_all(phase_all),
         .phase_0(phase_0),
         .phase_1(phase_1) );