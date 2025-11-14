// SystemVerilog Assertions for video_timing_gen
// Bind this checker to the DUT. Focused, high-signal-quality checks + useful coverage.

`ifndef VIDEO_TIMING_GEN_SVA
`define VIDEO_TIMING_GEN_SVA

module video_timing_gen_sva
  #(parameter H_SYNC_WIDTH = 96,
              H_BLANK_WIDTH = 208,
              V_SYNC_WIDTH = 2,
              V_BLANK_WIDTH = 35)
(
  // DUT ports
  input logic               aclk, rst,
  input logic               axis_tready, axis_tvalid,
  input logic [23:0]        axis_video,
  input logic [11:0]        active_pixels,
  input logic [11:0]        active_lines,
  input logic               video_clk, ce,
  input logic [11:0]        total_lines,
  input logic [11:0]        vsync_start, vsync_end,
  input logic [11:0]        total_pixels,
  input logic [11:0]        hsync_start, hsync_end,
  input logic               vtg_hsync, vtg_vsync, vtg_vblank, vtg_hblank, vtg_act_vid,
  input logic [1:0]         vtg_field_id,

  // DUT internals we want to check
  input logic [11:0]        line_count,
  input logic [11:0]        pixel_count,
  input logic [11:0]        total_pixels_reg,
  input logic [11:0]        total_lines_reg,
  input logic [11:0]        vsync_start_time,
  input logic [11:0]        vsync_end_time,
  input logic [11:0]        hsync_start_time,
  input logic [11:0]        hsync_end_time,
  input logic [1:0]         field_id_reg,
  input logic [7:0]         r, g, b
);

  default clocking cb @(posedge aclk); endclocking
  default disable iff (rst);

  // Reset behavior
  assert property (rst |=> (video_clk==0 && ce==0 &&
                            line_count==0 && pixel_count==0 &&
                            vsync_start_time==0 && vsync_end_time==0 &&
                            hsync_start_time==0 && hsync_end_time==0 &&
                            total_pixels_reg==0 && total_lines_reg==0 &&
                            field_id_reg==0 &&
                            vtg_hsync==0 && vtg_vsync==0 && vtg_vblank==0 && vtg_hblank==0 && vtg_act_vid==0 && vtg_field_id==0));

  // Counter integrity
  assert property (pixel_count < active_pixels);
  assert property (line_count <= (2*active_lines + 2*V_SYNC_WIDTH + V_BLANK_WIDTH));

  // Pixel count update and end-of-line pulse alignment
  assert property (1 |=> ( ($past(pixel_count)==active_pixels-1) -> (pixel_count==0) ) and
                          ( ($past(pixel_count)!=active_pixels-1) -> (pixel_count==$past(pixel_count)+1) ));
  assert property ($rose(video_clk) |-> (ce && $past(pixel_count)==active_pixels-1 && pixel_count==0));
  assert property (video_clk == ce);
  assert property ($rose(video_clk) |=> total_pixels_reg == $past(total_pixels_reg) + active_pixels);

  // Line wrap => total_lines increment
  assert property ((line_count==0 && $past(line_count)!=0) |=> total_lines_reg == $past(total_lines_reg) + 1);

  // Field ID toggles only on frame wrap; vtg_field_id tracks field_id_reg
  assert property ($changed(field_id_reg) |-> (line_count==0 && $past(line_count)!=0));
  assert property (vtg_field_id == field_id_reg);

  // AXIS capture: update only on handshake; and value correctness
  assert property (!(axis_tvalid && axis_tready) |-> $stable({r,g,b}));
  assert property ((axis_tvalid && axis_tready) |=> {r,g,b} == $past(axis_video));

  // Timing flags relationships (no invalid combinations)
  assert property (vtg_act_vid |-> (!vtg_vblank && !vtg_vsync));
  assert property (vtg_vblank |-> vtg_vsync);
  assert property (vtg_hblank |-> !vtg_hsync);
  assert property (!(vtg_hblank && vtg_act_vid));

  // Output wiring equals backing registers
  assert property (total_pixels == total_pixels_reg);
  assert property (total_lines  == total_lines_reg);
  assert property (vsync_start  == vsync_start_time);
  assert property (vsync_end    == vsync_end_time);
  assert property (hsync_start  == hsync_start_time);
  assert property (hsync_end    == hsync_end_time);

  // Coverage: key events
  cover property ($rose(video_clk));                          // end-of-line
  cover property (line_count==0 && $past(line_count)!=0);     // frame wrap
  cover property ($rose(vtg_vblank));                         // enter vblank
  cover property ($fell(vtg_vblank));                         // exit vblank
  cover property ($changed(field_id_reg));                    // field toggle
  cover property (axis_tvalid && axis_tready);                // AXIS transfer
  cover property (vtg_hblank);                                // hblank seen
  cover property ($changed(vsync_start_time));                // vsync start captured
  cover property ($changed(vsync_end_time));                  // vsync end captured
  cover property ($changed(hsync_start_time));                // hsync start captured
  cover property ($changed(hsync_end_time));                  // hsync end captured

endmodule

// Bind to all instances of video_timing_gen
bind video_timing_gen video_timing_gen_sva
  #(.H_SYNC_WIDTH(H_SYNC_WIDTH),
    .H_BLANK_WIDTH(H_BLANK_WIDTH),
    .V_SYNC_WIDTH(V_SYNC_WIDTH),
    .V_BLANK_WIDTH(V_BLANK_WIDTH))
  video_timing_gen_sva_i(
    // ports
    .aclk(aclk), .rst(rst),
    .axis_tready(axis_tready), .axis_tvalid(axis_tvalid),
    .axis_video(axis_video),
    .active_pixels(active_pixels), .active_lines(active_lines),
    .video_clk(video_clk), .ce(ce),
    .total_lines(total_lines),
    .vsync_start(vsync_start), .vsync_end(vsync_end),
    .total_pixels(total_pixels),
    .hsync_start(hsync_start), .hsync_end(hsync_end),
    .vtg_hsync(vtg_hsync), .vtg_vsync(vtg_vsync), .vtg_vblank(vtg_vblank), .vtg_hblank(vtg_hblank), .vtg_act_vid(vtg_act_vid),
    .vtg_field_id(vtg_field_id),

    // internals
    .line_count(line_count),
    .pixel_count(pixel_count),
    .total_pixels_reg(total_pixels_reg),
    .total_lines_reg(total_lines_reg),
    .vsync_start_time(vsync_start_time),
    .vsync_end_time(vsync_end_time),
    .hsync_start_time(hsync_start_time),
    .hsync_end_time(hsync_end_time),
    .field_id_reg(field_id_reg),
    .r(r), .g(g), .b(b)
  );

`endif