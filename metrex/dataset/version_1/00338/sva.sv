// SVA for sirv_gnrl_cdc_rx and sirv_gnrl_sync
// Concise, high-quality checks and coverage

// Bind into DUT (module-type bind)
bind sirv_gnrl_cdc_rx cdc_rx_sva #(.DW(DW), .SYNC_DP(SYNC_DP)) u_cdc_rx_sva (
  .clk(clk), .rst_n(rst_n),
  .i_vld_a(i_vld_a), .i_rdy(i_rdy), .i_dat(i_dat),
  .o_vld(o_vld), .o_rdy(o_rdy), .o_dat(o_dat),
  .i_vld_sync(u_i_vld_sync.dout), .i_vld_sync_r(i_vld_sync_r),
  .i_rdy_r(i_rdy_r), .i_rdy_set(i_rdy_set),
  .buf_vld_r(buf_vld_r), .buf_dat_r(buf_dat_r),
  .buf_dat_ena(buf_dat_ena), .buf_rdy(buf_rdy)
);

// Bind into synchronizer
bind sirv_gnrl_sync sync_sva #(.DP(DP), .DW(DW)) u_sync_sva (
  .clk(clk), .rst_n(rst_n), .din_a(din_a), .dout(dout)
);


// ---------- Assertions for sirv_gnrl_cdc_rx ----------
module cdc_rx_sva #(parameter DW=32, SYNC_DP=2)
(
  input clk, rst_n,
  input i_vld_a, input i_rdy, input [DW-1:0] i_dat,
  input o_vld, input o_rdy, input [DW-1:0] o_dat,
  input i_vld_sync, input i_vld_sync_r, input i_rdy_r, input i_rdy_set,
  input buf_vld_r, input [DW-1:0] buf_dat_r, input buf_dat_ena, input buf_rdy
);
  default clocking cb @(posedge clk); endclocking

  // Basic reset and X checks
  a_reset_low_outs: assert property (cb disable iff(1'b0) !rst_n |-> (!i_rdy && !o_vld));
  a_no_x_outs:      assert property (cb disable iff(!rst_n) !$isunknown({i_rdy,o_vld,o_dat}));

  // Structural equivalences/invariants
  a_bufrdy_equ:     assert property (cb disable iff(!rst_n) (o_vld == ~buf_rdy));
  a_sync_r_is_past: assert property (cb disable iff(!rst_n) (i_vld_sync_r == $past(i_vld_sync)));

  // Input-side 4-phase handshake semantics (on synchronized level)
  a_rdy_implies_sync:   assert property (cb disable iff(!rst_n) i_rdy |-> i_vld_sync);
  a_nosync_no_rdy:      assert property (cb disable iff(!rst_n) !i_vld_sync |-> !i_rdy);
  a_rise_rdy_when_ready:assert property (cb disable iff(!rst_n) $rose(i_rdy) |-> (buf_rdy && i_vld_sync && !$past(i_rdy)));
  a_fall_rdy_on_fall_v: assert property (cb disable iff(!rst_n) $fell(i_rdy) |-> $fell(i_vld_sync));

  // Buffer valid behavior and backpressure
  a_vld_holds_until_rdy:assert property (cb disable iff(!rst_n) (o_vld && !o_rdy) |=> o_vld);
  a_vld_drops_only_on_hs:assert property (cb disable iff(!rst_n) $fell(o_vld) |-> $past(o_vld && o_rdy));
  a_no_set_when_full:    assert property (cb disable iff(!rst_n) o_vld |-> !i_rdy_set);

  // Data path: load and stability
  a_load_causes_vld:     assert property (cb disable iff(!rst_n) $rose(o_vld) |-> $past(buf_dat_ena));
  a_data_captured:       assert property (cb disable iff(!rst_n) $rose(o_vld) |-> (o_dat == $past(i_dat)));
  a_data_stable_when_hold:assert property (cb disable iff(!rst_n) (o_vld && !o_rdy) |=> ($stable(o_dat)));
  a_bufdat_hold_no_ena:  assert property (cb disable iff(!rst_n) !buf_dat_ena |-> $stable(buf_dat_r));

  // Coverage: full 4-phase handshake (sync domain)
  c_4phase: cover property (cb disable iff(!rst_n)
    $rose(i_vld_sync) ##[0:$] $rose(i_rdy) ##[0:$] $fell(i_vld_sync) ##[0:$] $fell(i_rdy));

  // Coverage: backpressure then accept
  c_backpressure: cover property (cb disable iff(!rst_n)
    $rose(o_vld) ##[1:$] (o_vld && !o_rdy) ##[1:$] (o_vld && o_rdy) ##1 !o_vld);

  // Coverage: producer arrives while full, then serviced, then rdy granted
  c_arrival_while_full: cover property (cb disable iff(!rst_n)
    (o_vld && i_vld_sync) ##[1:$] (o_vld && o_rdy) ##1 !o_vld ##[0:$] $rose(i_rdy));

  // Coverage: back-to-back transfers
  c_b2b: cover property (cb disable iff(!rst_n)
    $rose(o_vld) ##[1:$] (o_vld && o_rdy) ##1 !o_vld ##[0:2] $rose(o_vld));

  // Coverage: data extremes
  c_data_zero: cover property (cb disable iff(!rst_n) $rose(o_vld) && (o_dat == '0));
  c_data_ones: cover property (cb disable iff(!rst_n) $rose(o_vld) && (&o_dat));
endmodule


// ---------- Assertions for sirv_gnrl_sync ----------
module sync_sva #(parameter DP=1, DW=1)
(
  input clk, rst_n,
  input din_a, input dout
);
  default clocking cb @(posedge clk); endclocking

  a_reset_low: assert property (cb disable iff(1'b0) !rst_n |-> !dout);
  a_no_x:      assert property (cb disable iff(!rst_n) !$isunknown({din_a,dout}));

  // If input is stable high/low long enough, output must match within DP cycles
  a_sync_high: assert property (cb disable iff(!rst_n)
    (din_a && $stable(din_a)[* (DP+1)]) |-> ##[0:DP] dout);

  a_sync_low:  assert property (cb disable iff(!rst_n)
    (!din_a && $stable(din_a)[* (DP+1)]) |-> ##[0:DP] !dout);

  // Coverage: rising and falling propagation within DP cycles
  c_rise_prog: cover property (cb disable iff(!rst_n) $rose(din_a) ##[1:DP] $rose(dout));
  c_fall_prog: cover property (cb disable iff(!rst_n) $fell(din_a) ##[1:DP] $fell(dout));
endmodule