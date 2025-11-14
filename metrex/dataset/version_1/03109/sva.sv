// SVA checker for vga. Bind this to the DUT.
// Focus: counter sequencing, ranges, sync timing/polarity, will_display, reset behavior, and coverage.
module vga_sva #(
  parameter HORIZONTAL_SYNC_POLARITY = 1'b0,
  parameter TIME_HORIZONTAL_VIDEO = 640,
  parameter TIME_HORIZONTAL_FRONT_PORCH = 16,
  parameter TIME_HORIZONTAL_SYNC_PULSE = 96,
  parameter TIME_HORIZONTAL_BACK_PORCH = 48,
  parameter TIME_HORIZONTAL =
      TIME_HORIZONTAL_VIDEO +
      TIME_HORIZONTAL_FRONT_PORCH +
      TIME_HORIZONTAL_SYNC_PULSE +
      TIME_HORIZONTAL_BACK_PORCH,
  parameter VERTICAL_SYNC_POLARITY = 1'b0,
  parameter TIME_VERTICAL_VIDEO = 480,
  parameter TIME_VERTICAL_FRONT_PORCH = 10,
  parameter TIME_VERTICAL_SYNC_PULSE = 2,
  parameter TIME_VERTICAL_BACK_PORCH = 33,
  parameter TIME_VERTICAL =
      TIME_VERTICAL_VIDEO +
      TIME_VERTICAL_FRONT_PORCH +
      TIME_VERTICAL_SYNC_PULSE +
      TIME_VERTICAL_BACK_PORCH
)(
  input  logic                         clk,
  input  logic                         reset,
  input  logic [$bits(TIME_HORIZONTAL)-1:0] h_counter,
  input  logic [$bits(TIME_VERTICAL)-1:0]   v_counter,
  input  logic [$bits(TIME_HORIZONTAL)-1:0] h_counter_next,
  input  logic [$bits(TIME_VERTICAL)-1:0]   v_counter_next,
  input  logic                         h_sync,
  input  logic                         v_sync,
  input  logic                         will_display
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Parameter sanity (compile/elab time)
  initial begin
    assert (TIME_HORIZONTAL > 0 && TIME_VERTICAL > 0);
  end

  // Range invariants (current and next)
  ap_hcnt_range: assert property (h_counter < TIME_HORIZONTAL);
  ap_vcnt_range: assert property (v_counter < TIME_VERTICAL);
  ap_hnxt_range: assert property (h_counter_next < TIME_HORIZONTAL);
  ap_vnxt_range: assert property (v_counter_next < TIME_VERTICAL);

  // Next-state combinational logic correctness
  ap_hnxt_inc:   assert property ((h_counter != TIME_HORIZONTAL-1) |-> h_counter_next == h_counter + 1);
  ap_hnxt_wrap:  assert property ((h_counter == TIME_HORIZONTAL-1) |-> h_counter_next == 0);
  ap_vnxt_hold:  assert property ((h_counter != TIME_HORIZONTAL-1) |-> v_counter_next == v_counter);
  ap_vnxt_step:  assert property ((h_counter == TIME_HORIZONTAL-1 && v_counter != TIME_VERTICAL-1) |-> v_counter_next == v_counter + 1);
  ap_vnxt_wrap:  assert property ((h_counter == TIME_HORIZONTAL-1 && v_counter == TIME_VERTICAL-1) |-> v_counter_next == 0);

  // Registered update equals previous "next"
  ap_q_follow_n_h: assert property (h_counter == $past(h_counter_next));
  ap_q_follow_n_v: assert property (v_counter == $past(v_counter_next));

  // Sequential behavior (independent of 'next' signals)
  ap_hcnt_seq_inc:  assert property ((h_counter != TIME_HORIZONTAL-1) |=> h_counter == $past(h_counter) + 1);
  ap_hcnt_seq_wrap: assert property ((h_counter == TIME_HORIZONTAL-1) |=> h_counter == 0);
  ap_vcnt_seq_hold: assert property ((h_counter != TIME_HORIZONTAL-1) |=> v_counter == $past(v_counter));
  ap_vcnt_seq_step: assert property ((h_counter == TIME_HORIZONTAL-1 && v_counter != TIME_VERTICAL-1) |=> v_counter == $past(v_counter) + 1);
  ap_vcnt_seq_wrap: assert property ((h_counter == TIME_HORIZONTAL-1 && v_counter == TIME_VERTICAL-1) |=> v_counter == 0);

  // Sync outputs match spec (polarity, position, width via equivalence)
  ap_hsync_def: assert property (
    h_sync == (((h_counter >= (TIME_HORIZONTAL_VIDEO + TIME_HORIZONTAL_FRONT_PORCH)) &&
                (h_counter <  (TIME_HORIZONTAL_VIDEO + TIME_HORIZONTAL_FRONT_PORCH + TIME_HORIZONTAL_SYNC_PULSE))))
              ? HORIZONTAL_SYNC_POLARITY : ~HORIZONTAL_SYNC_POLARITY)
  );
  ap_vsync_def: assert property (
    v_sync == (((v_counter >= (TIME_VERTICAL_VIDEO + TIME_VERTICAL_FRONT_PORCH)) &&
                (v_counter <  (TIME_VERTICAL_VIDEO + TIME_VERTICAL_FRONT_PORCH + TIME_VERTICAL_SYNC_PULSE))))
              ? VERTICAL_SYNC_POLARITY : ~VERTICAL_SYNC_POLARITY)
  );

  // Display region correctness
  ap_will_display_def: assert property (
    will_display == ((h_counter_next < TIME_HORIZONTAL_VIDEO) && (v_counter_next < TIME_VERTICAL_VIDEO))
  );

  // Reset behavior (synchronous loading through next)
  ap_rst_drives_next_zero: assert property (reset |-> (h_counter_next == 0 && v_counter_next == 0));
  ap_rst_sets_q_zero:      assert property (reset |=> (h_counter == 0 && v_counter == 0));
  ap_rst_holds_q_zero:     assert property ((reset && $past(reset)) |-> (h_counter == 0 && v_counter == 0));

  // Coverage
  // Basic regions
  cp_active_video:     cover property (will_display);
  cp_front_porch_h:    cover property (h_counter == TIME_HORIZONTAL_VIDEO && v_counter < TIME_VERTICAL_VIDEO);
  cp_sync_h_start:     cover property (h_counter == (TIME_HORIZONTAL_VIDEO + TIME_HORIZONTAL_FRONT_PORCH) && h_sync == HORIZONTAL_SYNC_POLARITY);
  cp_back_porch_h:     cover property (h_counter == (TIME_HORIZONTAL_VIDEO + TIME_HORIZONTAL_FRONT_PORCH + TIME_HORIZONTAL_SYNC_PULSE));
  cp_sync_v_start:     cover property (v_counter == (TIME_VERTICAL_VIDEO + TIME_VERTICAL_FRONT_PORCH) && v_sync == VERTICAL_SYNC_POLARITY);

  // Line and frame boundaries
  cp_line_wrap:        cover property (h_counter == TIME_HORIZONTAL-1 ##1 h_counter == 0);
  cp_frame_wrap:       cover property ((h_counter == TIME_HORIZONTAL-1 && v_counter == TIME_VERTICAL-1) ##1 (h_counter == 0 && v_counter == 0));

  // will_display edges
  cp_disp_rise:        cover property (!will_display ##1 will_display);
  cp_disp_fall:        cover property (will_display ##1 !will_display);

  // Corners of active area (using next-state which defines will_display)
  cp_top_left:         cover property (h_counter_next == 0 && v_counter_next == 0 && will_display);
  cp_bottom_right:     cover property (h_counter_next == TIME_HORIZONTAL_VIDEO-1 &&
                                       v_counter_next == TIME_VERTICAL_VIDEO-1 && will_display);
endmodule

// Bind into every instance of vga
bind vga vga_sva #(
  .HORIZONTAL_SYNC_POLARITY(HORIZONTAL_SYNC_POLARITY),
  .TIME_HORIZONTAL_VIDEO(TIME_HORIZONTAL_VIDEO),
  .TIME_HORIZONTAL_FRONT_PORCH(TIME_HORIZONTAL_FRONT_PORCH),
  .TIME_HORIZONTAL_SYNC_PULSE(TIME_HORIZONTAL_SYNC_PULSE),
  .TIME_HORIZONTAL_BACK_PORCH(TIME_HORIZONTAL_BACK_PORCH),
  .TIME_HORIZONTAL(TIME_HORIZONTAL),
  .VERTICAL_SYNC_POLARITY(VERTICAL_SYNC_POLARITY),
  .TIME_VERTICAL_VIDEO(TIME_VERTICAL_VIDEO),
  .TIME_VERTICAL_FRONT_PORCH(TIME_VERTICAL_FRONT_PORCH),
  .TIME_VERTICAL_SYNC_PULSE(TIME_VERTICAL_SYNC_PULSE),
  .TIME_VERTICAL_BACK_PORCH(TIME_VERTICAL_BACK_PORCH),
  .TIME_VERTICAL(TIME_VERTICAL)
) u_vga_sva (
  .clk(clk),
  .reset(reset),
  .h_counter(h_counter),
  .v_counter(v_counter),
  .h_counter_next(h_counter_next),
  .v_counter_next(v_counter_next),
  .h_sync(h_sync),
  .v_sync(v_sync),
  .will_display(will_display)
);