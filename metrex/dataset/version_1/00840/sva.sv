// SVA checker for rr_event_picker
// Bind this module to the DUT to verify functionality and provide concise coverage.

module rr_event_picker_sva (
  input  logic        rclk,
  input  logic        arst_l,
  input  logic        grst_l,
  input  logic        se,

  input  logic [3:0]  events,
  input  logic [3:0]  events_picked,
  input  logic [3:0]  thread_force,
  input  logic [3:0]  pick_one_hot,

  // internal DUT nets/regs (bound hierarchically)
  input  logic        reset,
  input  logic        dbb_reset_l,
  input  logic        dbb_rstff_Q,

  input  logic [3:0]  pick_rrobin,
  input  logic [3:0]  pick_rrobin_din,
  input  logic [3:0]  pick_rrobin_events,
  input  logic        pick_rrobin_reset,
  input  logic        pick_rrobin_dir_upd,

  input  logic [3:0]  pick_rrobin_1hot,
  input  logic [3:0]  pick_rev_rrobin_1hot,
  input  logic [3:0]  pick_rrobin_1hot_mx,

  input  logic        thread_force_events_sel,
  input  logic [3:0]  pick_thread_force_1hot,

  input  logic        events_pick_dir,
  input  logic        events_pick_dir_d1
);

  default clocking cb @(posedge rclk); endclocking

  // Basic sanity
  a_no_x_on_pick:        assert property (!$isunknown(pick_one_hot));
  a_onehot0_pick:        assert property ($onehot0(pick_one_hot));
  a_subset_events:       assert property (((pick_one_hot & ~events) == 4'b0));
  a_no_events_no_pick:   assert property ((events == 4'b0) |-> (pick_one_hot == 4'b0));

  // Thread-force path
  logic [3:0] tf_mask;
  assign tf_mask = (events & thread_force);

  a_tf_sel_mux:          assert property (thread_force_events_sel |-> (pick_one_hot == pick_thread_force_1hot));
  a_tf_subset_mask:      assert property (thread_force_events_sel |-> ((pick_one_hot & ~tf_mask) == 4'b0));
  a_tf_onehot0:          assert property ($onehot0(pick_thread_force_1hot));

  a_tf0:                 assert property (thread_force_events_sel && tf_mask[0]                                 |-> (pick_one_hot == 4'b0001));
  a_tf1:                 assert property (thread_force_events_sel && ~tf_mask[0]      && tf_mask[1]             |-> (pick_one_hot == 4'b0010));
  a_tf2:                 assert property (thread_force_events_sel && ~|tf_mask[1:0]   && tf_mask[2]             |-> (pick_one_hot == 4'b0100));
  a_tf3:                 assert property (thread_force_events_sel && ~|tf_mask[2:0]   && tf_mask[3]             |-> (pick_one_hot == 4'b1000));

  // Round-robin path muxing and onehot
  a_rr_sel_mux:          assert property (!thread_force_events_sel |-> (pick_one_hot == pick_rrobin_1hot_mx));
  a_rr_onehot0:          assert property ($onehot0(pick_rrobin_1hot_mx));
  a_rr_subset_ev:        assert property (((pick_rrobin_1hot_mx & ~pick_rrobin_events) == 4'b0));

  // RR event formation
  a_rrevents_def:        assert property (pick_rrobin_events == (events & ~pick_rrobin));

  // RR pick direction and chosen bit (forward priority: 0->3)
  a_rr_fwd_0:            assert property (!thread_force_events_sel && !events_pick_dir_d1 &&  pick_rrobin_events[0]                                  |-> (pick_one_hot == 4'b0001));
  a_rr_fwd_1:            assert property (!thread_force_events_sel && !events_pick_dir_d1 && ~pick_rrobin_events[0] && pick_rrobin_events[1]        |-> (pick_one_hot == 4'b0010));
  a_rr_fwd_2:            assert property (!thread_force_events_sel && !events_pick_dir_d1 && ~|pick_rrobin_events[1:0] && pick_rrobin_events[2]     |-> (pick_one_hot == 4'b0100));
  a_rr_fwd_3:            assert property (!thread_force_events_sel && !events_pick_dir_d1 && ~|pick_rrobin_events[2:0] && pick_rrobin_events[3]     |-> (pick_one_hot == 4'b1000));

  // RR pick direction and chosen bit (reverse priority: 3->0)
  a_rr_rev_3:            assert property (!thread_force_events_sel &&  events_pick_dir_d1 &&  pick_rrobin_events[3]                                  |-> (pick_one_hot == 4'b1000));
  a_rr_rev_2:            assert property (!thread_force_events_sel &&  events_pick_dir_d1 && ~pick_rrobin_events[3] && pick_rrobin_events[2]        |-> (pick_one_hot == 4'b0100));
  a_rr_rev_1:            assert property (!thread_force_events_sel &&  events_pick_dir_d1 && ~|pick_rrobin_events[3:2] && pick_rrobin_events[1]     |-> (pick_one_hot == 4'b0010));
  a_rr_rev_0:            assert property (!thread_force_events_sel &&  events_pick_dir_d1 && ~|pick_rrobin_events[3:1] && pick_rrobin_events[0]     |-> (pick_one_hot == 4'b0001));

  // RR state machine/control relations
  a_rr_reset_def:        assert property (pick_rrobin_reset == (reset | ~|(events & ~(pick_rrobin | events_picked))));
  a_rr_dirupd_def:       assert property (pick_rrobin_dir_upd == (|events & (~|(events & ~(pick_rrobin | events_picked)))));
  a_dir_def:             assert property (events_pick_dir == (~reset & (events_pick_dir_d1 ^ pick_rrobin_dir_upd)));

  // RR DIN formation
  a_din_reset_zero:      assert property (pick_rrobin_reset |-> (pick_rrobin_din == 4'b0000));
  a_din_dirupd_rotate:   assert property (!pick_rrobin_reset && pick_rrobin_dir_upd |-> (pick_rrobin_din == {pick_rrobin_events[2:0], pick_rrobin_events[3]}));
  a_din_else_events:     assert property (!pick_rrobin_reset && !pick_rrobin_dir_upd |-> (pick_rrobin_din == pick_rrobin_events));

  // Sequential updates (note: 'reset' is used asymmetrically in DUT by design)
  a_rrflop_clr_on_nreset: assert property ((!reset) |=> (pick_rrobin == 4'b0000));
  a_rrflop_load_on_reset: assert property (( reset) |=> (pick_rrobin == $past(pick_rrobin_din)));

  a_dirflop_clr_on_reset: assert property (( reset) |=> (events_pick_dir_d1 == 1'b0));
  a_dirflop_load_else:    assert property ((!reset) |=> (events_pick_dir_d1 == $past(events_pick_dir)));

  // Reset tree flop behavior and derived resets
  a_dbb_reset_wire:      assert property (dbb_reset_l == dbb_rstff_Q);
  a_reset_def:           assert property (reset == ~dbb_reset_l);
  a_dbb_rstff_seq:       assert property (dbb_rstff_Q == (($past(~arst_l | grst_l)) & ($past(dbb_rstff_Q) & ~$past(se))));

  // Coverage
  c_pick_bit0:           cover property (pick_one_hot == 4'b0001);
  c_pick_bit1:           cover property (pick_one_hot == 4'b0010);
  c_pick_bit2:           cover property (pick_one_hot == 4'b0100);
  c_pick_bit3:           cover property (pick_one_hot == 4'b1000);

  c_tf_path:             cover property (thread_force_events_sel && (pick_one_hot != 4'b0));
  c_rr_path:             cover property (!thread_force_events_sel && (pick_one_hot != 4'b0));

  c_dir_toggle:          cover property (pick_rrobin_dir_upd ##1 (events_pick_dir_d1 != $past(events_pick_dir_d1)));
  c_rr_reset:            cover property (pick_rrobin_reset);

endmodule

// Bind example (place in a package or a testbench file)
bind rr_event_picker rr_event_picker_sva i_rr_event_picker_sva (
  .rclk                    (rclk),
  .arst_l                  (arst_l),
  .grst_l                  (grst_l),
  .se                      (se),

  .events                  (events),
  .events_picked           (events_picked),
  .thread_force            (thread_force),
  .pick_one_hot            (pick_one_hot),

  .reset                   (reset),
  .dbb_reset_l             (dbb_reset_l),
  .dbb_rstff_Q             (dbb_rstff_Q),

  .pick_rrobin             (pick_rrobin),
  .pick_rrobin_din         (pick_rrobin_din),
  .pick_rrobin_events      (pick_rrobin_events),
  .pick_rrobin_reset       (pick_rrobin_reset),
  .pick_rrobin_dir_upd     (pick_rrobin_dir_upd),

  .pick_rrobin_1hot        (pick_rrobin_1hot),
  .pick_rev_rrobin_1hot    (pick_rev_rrobin_1hot),
  .pick_rrobin_1hot_mx     (pick_rrobin_1hot_mx),

  .thread_force_events_sel (thread_force_events_sel),
  .pick_thread_force_1hot  (pick_thread_force_1hot),

  .events_pick_dir         (events_pick_dir),
  .events_pick_dir_d1      (events_pick_dir_d1)
);