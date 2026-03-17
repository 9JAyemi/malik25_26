// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_ar_flags_mutex, assert, property, negedge, disable, iff, initstate, check_ar_flags_stable_without_load, past, check_ar_flags_after_load_pos, b1, b0, check_ar_flags_after_load_neg, check_ar_flags_after_load_zero, check_ar_flags_after_load_nonzero_onehot, check_cr_hold_on_load, check_cr_hold_when_no_ops, check_cr_clear_when_only_clr, sd0, check_cr_zero_persistent_on_only_clr
bind Datapath_Unit Datapath_Unit_sva auto_sva_inst (
    .CR(CR),
    .AR_gt_0(AR_gt_0),
    .AR_lt_0(AR_lt_0),
    .Data_AR(Data_AR),
    .Data_BR(Data_BR),
    .Ld_AR_BR(Ld_AR_BR),
    .Div_AR_x2_CR(Div_AR_x2_CR),
    .Mul_BR_x2_CR(Mul_BR_x2_CR),
    .Clr_CR(Clr_CR),
    .clk(clk)
);
