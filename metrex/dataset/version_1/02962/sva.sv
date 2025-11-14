// SVA for fscmos. Bind this module to the DUT.
module fscmos_sva #
(
  parameter int C_IN_WIDTH  = 8,
  parameter int C_OUT_WIDTH = 8
)
(
  input  wire                 cmos_pclk,
  input  wire                 cmos_vsync,
  input  wire                 cmos_href,
  input  wire [C_IN_WIDTH-1:0]  cmos_data,

  input  wire                 vid_active_video,
  input  wire [C_OUT_WIDTH-1:0] vid_data,
  input  wire                 vid_hblank,
  input  wire                 vid_hsync,
  input  wire                 vid_vblank,
  input  wire                 vid_vsync
);

  default clocking cb @ (posedge cmos_pclk); endclocking

  // Basic sanity on params (static)
  initial begin
    assert (C_IN_WIDTH > 0 && C_OUT_WIDTH > 0)
      else $error("C_IN_WIDTH/C_OUT_WIDTH must be > 0");
  end

  // No X/Z on outputs when inputs known
  a_known_ctrl: assert property (!$isunknown({cmos_href,cmos_vsync})) |->
                                  !$isunknown({vid_active_video,vid_hblank,vid_hsync,vid_vblank,vid_vsync});
  a_known_data: assert property (!$isunknown(cmos_data)) |->
                                  !$isunknown(vid_data);

  // Functional equivalence
  a_active_video: assert property (vid_active_video === (cmos_href && !cmos_vsync));
  a_hblank:       assert property (vid_hblank       === !cmos_href);
  a_hsync_eq_hb:  assert property (vid_hsync        === vid_hblank);
  a_vblank:       assert property (vid_vblank       === !cmos_vsync);
  a_vsync_eq_vb:  assert property (vid_vsync        === vid_vblank);

  // Combinational stability: if inputs stable, outputs stable
  a_stable: assert property ($stable({cmos_href,cmos_vsync,cmos_data})) |->
                             $stable({vid_active_video,vid_hblank,vid_hsync,vid_vblank,vid_vsync,vid_data});

  // Data path mapping by parameterization
  generate
    if (C_IN_WIDTH < C_OUT_WIDTH) begin : g_pad
      a_data_hi_map:  assert property (vid_data[C_OUT_WIDTH-1 -: C_IN_WIDTH] === cmos_data);
      a_data_lo_zero: assert property (vid_data[C_OUT_WIDTH-C_IN_WIDTH-1:0] == '0);
    end
    else begin : g_trunc
      a_data_trunc: assert property (vid_data === cmos_data[C_IN_WIDTH-1 -: C_OUT_WIDTH]);
    end
  endgenerate

  // Coverage: exercise key states/edges and datapath activity
  c_av_on:           cover property (vid_active_video);
  c_av_off_href0:    cover property (!cmos_href && !vid_active_video);
  c_av_off_vsync1:   cover property ( cmos_vsync && !vid_active_video);
  c_hblank_edges_r:  cover property ($rose(vid_hblank));
  c_hblank_edges_f:  cover property ($fell(vid_hblank));
  c_vblank_edges_r:  cover property ($rose(vid_vblank));
  c_vblank_edges_f:  cover property ($fell(vid_vblank));
  c_data_change:     cover property ($changed(vid_data));

endmodule

// Bind to DUT
bind fscmos fscmos_sva #(.C_IN_WIDTH(C_IN_WIDTH), .C_OUT_WIDTH(C_OUT_WIDTH)) fscmos_sva_i (
  .cmos_pclk,
  .cmos_vsync,
  .cmos_href,
  .cmos_data,
  .vid_active_video,
  .vid_data,
  .vid_hblank,
  .vid_hsync,
  .vid_vblank,
  .vid_vsync
);