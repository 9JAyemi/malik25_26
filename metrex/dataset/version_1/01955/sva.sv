// SVA for edgedetect
module edgedetect_sva #(parameter string registered = "FALSE")
(
  input logic iCLK,
  input logic iRST,
  input logic iSIG,
  input logic oRE,
  input logic oFE,
  input logic oRFE,
  input logic delay,
  input logic re,
  input logic fe,
  input logic rfe,
  input logic re_reg,
  input logic fe_reg,
  input logic rfe_reg
);

  default clocking cb @(posedge iCLK); endclocking

  // State/reset behavior
  a_delay_rst:  assert property (iRST |-> delay==1'b0);
  a_regs_rst:   assert property (iRST |-> (re_reg==0 && fe_reg==0 && rfe_reg==0));

  // Sequential tracking
  a_delay_cap:  assert property (disable iff (iRST) delay == $past(iSIG));
  a_regs_track: assert property (disable iff (iRST)
                                 (re_reg==$past(re) && fe_reg==$past(fe) && rfe_reg==$past(rfe)));

  // Combinational correctness
  a_re_comb:    assert property (re  == (iSIG && !delay));
  a_fe_comb:    assert property (fe  == (!iSIG && delay));
  a_rfe_xor:    assert property (rfe == (iSIG ^ delay));
  a_rfe_or:     assert property (rfe == (re || fe));
  a_int_excl:   assert property (!(re && fe));

  // Output selection and timing
  if (registered == "TRUE") begin
    a_out_sel_true:  assert property (oRE==re_reg && oFE==fe_reg && oRFE==rfe_reg);
    a_out_rst_true:  assert property (iRST |-> (oRE==0 && oFE==0 && oRFE==0));
    a_re_edge_true:  assert property ($past(!iRST) && $rose(iSIG)   |=> oRE);
    a_fe_edge_true:  assert property ($past(!iRST) && $fell(iSIG)   |=> oFE);
    a_rfe_edge_true: assert property ($past(!iRST) && $changed(iSIG) |=> oRFE);
  end else begin
    a_out_sel_false: assert property (oRE==re && oFE==fe && oRFE==rfe);
    a_re_edge_false: assert property ($past(!iRST) && $rose(iSIG)   |-> oRE);
    a_fe_edge_false: assert property ($past(!iRST) && $fell(iSIG)   |-> oFE);
    a_rfe_edge_false:assert property ($past(!iRST) && $changed(iSIG)|-> oRFE);
  end

  // Output relations and pulse shapes
  a_out_excl:    assert property (disable iff (iRST) !(oRE && oFE));
  a_orfe_or:     assert property (disable iff (iRST) oRFE == (oRE || oFE));
  a_re_pulse1:   assert property (disable iff (iRST) oRE  |=> !oRE);
  a_fe_pulse1:   assert property (disable iff (iRST) oFE  |=> !oFE);
  a_rfe_pulse1:  assert property (disable iff (iRST) oRFE |=> !oRFE);
  a_no_pulse_stable: assert property ($past(!iRST) && !$changed(iSIG) |-> (!oRE && !oFE && !oRFE));

  // Coverage
  cover_re:       cover property (disable iff (iRST) oRE);
  cover_fe:       cover property (disable iff (iRST) oFE);
  cover_rfe:      cover property (disable iff (iRST) oRFE);
  cover_r_then_f: cover property (disable iff (iRST) oRE ##1 oFE);
  cover_f_then_r: cover property (disable iff (iRST) oFE ##1 oRE);

endmodule

bind edgedetect edgedetect_sva #(.registered(registered)) edgedetect_sva_i
(
  .iCLK(iCLK),
  .iRST(iRST),
  .iSIG(iSIG),
  .oRE(oRE),
  .oFE(oFE),
  .oRFE(oRFE),
  .delay(delay),
  .re(re),
  .fe(fe),
  .rfe(rfe),
  .re_reg(re_reg),
  .fe_reg(fe_reg),
  .rfe_reg(rfe_reg)
);