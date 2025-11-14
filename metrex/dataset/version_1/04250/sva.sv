// SVA for de3d_tc_mc_we
// Bind these directly to the DUT so internal cs is visible

// Sanity: no X/Z on key signals at sample time
bind de3d_tc_mc_we
  assert property (@(posedge mclock) !$isunknown({rstn, tex_push_en, ram_sel, cs, ram_wen_lo, ram_wen_hi}));

// Asynchronous reset immediately clears cs
bind de3d_tc_mc_we
  assert property (@(negedge rstn) cs == 1'b0);

// Next-state: cs toggles iff tex_push_en is 1; holds otherwise
bind de3d_tc_mc_we
  assert property (@(posedge mclock) $past(rstn) |-> cs == ($past(cs) ^ $past(tex_push_en)));

// Combinational write enables implement XOR/XNOR gating with tex_push_en
bind de3d_tc_mc_we
  assert property (@(posedge mclock) ram_wen_hi == (tex_push_en &  (cs ^ ram_sel)));
bind de3d_tc_mc_we
  assert property (@(posedge mclock) ram_wen_lo == (tex_push_en & ~(cs ^ ram_sel)));

// Mutual exclusivity and correct relationship to tex_push_en
bind de3d_tc_mc_we
  assert property (@(posedge mclock) (ram_wen_lo ^ ram_wen_hi) == tex_push_en);
bind de3d_tc_mc_we
  assert property (@(posedge mclock) !(ram_wen_lo && ram_wen_hi));
bind de3d_tc_mc_we
  assert property (@(posedge mclock) (ram_wen_lo || ram_wen_hi) |-> tex_push_en);

// Coverage: both write-enable polarities exercised
bind de3d_tc_mc_we
  cover property (@(posedge mclock) rstn && tex_push_en && (cs ^ ram_sel) == 1'b0 && ram_wen_lo && !ram_wen_hi);
bind de3d_tc_mc_we
  cover property (@(posedge mclock) rstn && tex_push_en && (cs ^ ram_sel) == 1'b1 && ram_wen_hi && !ram_wen_lo);

// Coverage: cs toggles on push from both states
bind de3d_tc_mc_we
  cover property (@(posedge mclock) $past(rstn) && $rose(tex_push_en) && $past(cs)==1'b0 && cs==1'b1);
bind de3d_tc_mc_we
  cover property (@(posedge mclock) $past(rstn) && $rose(tex_push_en) && $past(cs)==1'b1 && cs==1'b0);