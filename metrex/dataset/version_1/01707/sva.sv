// SVA checker for NV_NVDLA_CACC_CALC_int8
// Bind this module to the DUT (bind statement at end)

module NV_NVDLA_CACC_CALC_int8_sva (
  input logic              nvdla_core_clk,
  input logic              nvdla_core_rstn,

  // DUT ports
  input logic [4:0]        cfg_truncate,
  input logic [21:0]       in_data,
  input logic [33:0]       in_op,
  input logic              in_op_valid,
  input logic              in_sel,
  input logic              in_valid,
  input logic [31:0]       out_final_data,
  input logic              out_final_sat,
  input logic              out_final_valid,
  input logic [33:0]       out_partial_data,
  input logic              out_partial_valid,

  // DUT internals
  input logic [21:0]       di_pd,
  input logic [33:0]       oi_pd,
  input logic              i_vld,
  input logic              i_sel,
  input logic              i_sat_vld,
  input logic              i_sat_sel,
  input logic [34:0]       i_sum_pd,
  input logic              i_sum_sign,
  input logic              i_sum_msb,
  input logic              i_sat_sign,
  input logic [32:0]       i_sat_bits,
  input logic [33:0]       i_sat_pd,
  input logic [33:0]       i_partial_result,
  input logic [33:0]       i_pre_sft_pd,
  input logic [33:0]       i_sft_pd,
  input logic              i_guide,
  input logic [14:0]       i_stick,
  input logic              i_point5,
  input logic              mon_pos_pd_c,
  input logic [31:0]       i_pos_pd,
  input logic [31:0]       i_tru_pd,
  input logic              i_sft_need_sat,
  input logic [31:0]       i_sft_max,
  input logic [31:0]       i_final_result,
  input logic              i_partial_vld,
  input logic              i_final_vld
);

  default clocking cb @(posedge nvdla_core_clk); endclocking
  default disable iff (!nvdla_core_rstn)

  // Basic sanity / reset
  a_no_x_inputs:       assert property (!$isunknown({in_valid,in_sel,in_op_valid,cfg_truncate})));
  a_no_x_out_when_vld: assert property (out_partial_valid |-> !$isunknown(out_partial_data));
  a_no_x_final_when_vld: assert property (out_final_valid |-> !$isunknown({out_final_data,out_final_sat})));
  a_reset_outs_zero:   assert property (!nvdla_core_rstn |-> (!out_partial_valid && !out_final_valid && !out_final_sat));

  // Combinational mask path
  a_mask_oi_pd: assert property (oi_pd == (in_op_valid ? in_op[33:0] : 34'b0));
  a_sel_alias:  assert property (i_sel == in_sel);
  a_vld_alias:  assert property (i_vld == in_valid);

  // Pipe/control timing (use $past after one clean cycle of reset)
  a_sat_vld_pipe: assert property ($past(nvdla_core_rstn) |-> i_sat_vld == $past(i_vld));
  a_sat_sel_pipe: assert property ($past(nvdla_core_rstn) && $past(i_vld) |-> i_sat_sel == $past(i_sel));

  // Sum datapath update
  a_sum_update: assert property ($past(nvdla_core_rstn) && $past(i_vld) |->
                                 i_sum_pd == $signed($past(di_pd)) + $signed($past(oi_pd)));

  // Saturation pre-processing
  a_sat_pack: assert property (i_sat_pd == { i_sum_sign
                                           , (i_sum_sign ^ i_sum_msb) ? {33{~i_sum_sign}} : i_sum_pd[32:0] });
  a_partial_is_satpd: assert property (i_partial_result == i_sat_pd);

  // Shift/truncate pack (guide and stick)
  a_shift_pack: assert property ({i_sft_pd, i_guide, i_stick} ==
                                 ($signed({i_pre_sft_pd,16'b0}) >>> cfg_truncate));

  // Rounding add
  a_pos_add: assert property ({mon_pos_pd_c, i_pos_pd} == (i_sft_pd[31:0] + i_point5));
  a_tru_alias: assert property (i_tru_pd == i_pos_pd);

  // Final select (saturate vs true)
  a_final_sel: assert property (i_final_result == (i_sft_need_sat ? i_sft_max : i_tru_pd));

  // Valid generation and exclusivity
  a_partial_vld_def: assert property (i_partial_vld == (i_sat_vld && !i_sat_sel));
  a_final_vld_def:   assert property (i_final_vld   == (i_sat_vld &&  i_sat_sel));
  a_vld_excl:        assert property (!(i_partial_vld && i_final_vld));
  a_vld_cover_all:   assert property ((i_partial_vld || i_final_vld) == i_sat_vld);

  // Output register timing
  a_out_pvld_pipe: assert property ($past(nvdla_core_rstn) |-> out_partial_valid == $past(i_partial_vld));
  a_out_fvld_pipe: assert property ($past(nvdla_core_rstn) |-> out_final_valid   == $past(i_final_vld));
  a_out_psat_pipe: assert property ($past(nvdla_core_rstn) |-> out_final_sat     == $past(i_final_vld && i_sft_need_sat));

  // Output data update on valid
  a_out_pdata: assert property ($past(nvdla_core_rstn) && $past(i_partial_vld) |-> out_partial_data == $past(i_partial_result));
  a_out_fdata: assert property ($past(nvdla_core_rstn) && $past(i_final_vld)   |-> out_final_data   == $past(i_final_result));

  // Consistency: sat flag implies valid
  a_sat_implies_valid: assert property (out_final_sat |-> out_final_valid);

  // Corner/functional coverage
  c_partial_path:  cover property (i_partial_vld);
  c_final_path:    cover property (i_final_vld);
  c_mask_zero:     cover property (!in_op_valid && i_vld);
  c_mask_used:     cover property ( in_op_valid && i_vld);
  c_select0:       cover property (i_vld && !i_sel);
  c_select1:       cover property (i_vld &&  i_sel);
  c_trunc0:        cover property (i_vld && cfg_truncate==5'd0);
  c_trunc31:       cover property (i_vld && cfg_truncate==5'd31);
  c_round_point5:  cover property (i_point5 && i_sat_sel && i_final_vld);
  c_no_round:      cover property (!i_point5 && i_sat_sel && i_final_vld);
  c_saturate_pos:  cover property (i_sft_need_sat && !i_sat_sign && i_final_vld);
  c_saturate_neg:  cover property (i_sft_need_sat &&  i_sat_sign && i_final_vld);
  c_nosat_final:   cover property (!i_sft_need_sat && i_final_vld);

endmodule

// Bind into DUT (tool must allow hierarchical binding of internals)
bind NV_NVDLA_CACC_CALC_int8 NV_NVDLA_CACC_CALC_int8_sva i_NV_NVDLA_CACC_CALC_int8_sva (
  .nvdla_core_clk   (nvdla_core_clk),
  .nvdla_core_rstn  (nvdla_core_rstn),

  .cfg_truncate     (cfg_truncate),
  .in_data          (in_data),
  .in_op            (in_op),
  .in_op_valid      (in_op_valid),
  .in_sel           (in_sel),
  .in_valid         (in_valid),
  .out_final_data   (out_final_data),
  .out_final_sat    (out_final_sat),
  .out_final_valid  (out_final_valid),
  .out_partial_data (out_partial_data),
  .out_partial_valid(out_partial_valid),

  .di_pd            (di_pd),
  .oi_pd            (oi_pd),
  .i_vld            (i_vld),
  .i_sel            (i_sel),
  .i_sat_vld        (i_sat_vld),
  .i_sat_sel        (i_sat_sel),
  .i_sum_pd         (i_sum_pd),
  .i_sum_sign       (i_sum_sign),
  .i_sum_msb        (i_sum_msb),
  .i_sat_sign       (i_sat_sign),
  .i_sat_bits       (i_sat_bits),
  .i_sat_pd         (i_sat_pd),
  .i_partial_result (i_partial_result),
  .i_pre_sft_pd     (i_pre_sft_pd),
  .i_sft_pd         (i_sft_pd),
  .i_guide          (i_guide),
  .i_stick          (i_stick),
  .i_point5         (i_point5),
  .mon_pos_pd_c     (mon_pos_pd_c),
  .i_pos_pd         (i_pos_pd),
  .i_tru_pd         (i_tru_pd),
  .i_sft_need_sat   (i_sft_need_sat),
  .i_sft_max        (i_sft_max),
  .i_final_result   (i_final_result),
  .i_partial_vld    (i_partial_vld),
  .i_final_vld      (i_final_vld)
);