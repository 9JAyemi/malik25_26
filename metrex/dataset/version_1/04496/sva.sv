// SVA for mgc_out_reg_pos
// Concise, checks key behaviors incl. reset, enable, data path, and the intended lz_r_dly pipeline.

module mgc_out_reg_pos_sva #(
  parameter int width   = 8,
  parameter bit ph_en   = 1'b1,
  parameter bit ph_arst = 1'b0,
  parameter bit ph_srst = 1'b0
)(
  input  logic                 clk,
  input  logic                 en,
  input  logic                 arst,
  input  logic                 srst,
  input  logic                 ld,
  input  logic  [width-1:0]    d,
  input  logic                 lz,
  input  logic  [width-1:0]    z,

  // internal DUT signals
  input  logic                 lz_r,
  input  logic  [width-1:0]    z_r,
  input  logic                 lz_r_dly
);

  default clocking cb @(posedge clk); endclocking

  // Active-level helpers
  wire arst_act = (arst == ph_arst);
  wire srst_act = (srst == ph_srst);
  wire en_act   = (en   == ph_en);

  // Synchronous async-reset block behavior
  // On asserted arst, next-cycle lz_r and z_r are cleared
  a_arst_sync_clr: assert property (arst_act |=> (lz_r == 1'b0 && z_r == '0));

  // Enable behavior for lz_r/z_r
  a_en_loads:     assert property (!arst_act && en_act   |=> (lz_r == ld && z_r == d));
  a_en_holds:     assert property (!arst_act && !en_act  |=> ($stable(lz_r) && $stable(z_r)));

  // lz mirrors lz_r
  a_lz_is_lz_r:   assert property (lz === lz_r);

  // z register behavior
  // Synchronous srst clears z next cycle
  a_srst_sync_clr: assert property (srst_act |=> (z == '0));
  // Otherwise, z takes previous-cycle mux of lz_r_dly and z_r
  a_z_path:        assert property (!srst_act |=> (z == ($past(lz_r_dly) ? '0 : $past(z_r))));

  // Intended pipeline: lz_r_dly should be prior-cycle lz_r (would fail with current RTL)
  a_lz_dly_pipe:   assert property (disable iff (arst_act) (lz_r_dly == $past(lz_r)));

  // Simple X/Z sanitization on outputs
  a_no_x_outs:     assert property (!$isunknown({lz, z}));

  // Compact functional coverage
  c_load:          cover property (!arst_act && en_act   ##1 (lz_r == ld && z_r == d));
  c_arst:          cover property (arst_act              ##1 (lz_r == 1'b0 && z_r == '0));
  c_srst:          cover property (srst_act              ##1 (z == '0));
  // Cover intended zeroing via lz_r_dly gating
  c_zero_via_lzdly: cover property (!srst_act ##1 ($past(lz_r_dly) && z == '0));

endmodule

// Bind into the DUT to access internals
bind mgc_out_reg_pos mgc_out_reg_pos_sva #(
  .width(width),
  .ph_en(ph_en),
  .ph_arst(ph_arst),
  .ph_srst(ph_srst)
) mgc_out_reg_pos_sva_i (
  .clk(clk),
  .en(en),
  .arst(arst),
  .srst(srst),
  .ld(ld),
  .d(d),
  .lz(lz),
  .z(z),
  .lz_r(lz_r),
  .z_r(z_r),
  .lz_r_dly(lz_r_dly)
);