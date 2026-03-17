// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): reset_state_idle, assert, property, reset_outputs_idle, b1, b0, check_state_uses_newstate, disable, iff, past, nextstate_calc_idle, nextstate_calc_mul, nextstate_calc_done, check_done_decode, check_ld_decode, check_shift_decode, check_shift_vs_outputs, check_ld_done_mutex, done_next_depends_on_start, ld_holds_when_start_low, ld_clears_when_start_high, mul_to_done_on_start_and_proddone, mul_stay_when_start_and_not_proddone, mul_to_idle_when_start_low, done_rise_from_mul_start_proddone, rose, ld_fall_requires_start_high, fell, ld_rise_requires_start_low, done_fall_requires_start_low
bind multifsm multifsm_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .proddone(proddone),
    .start(start),
    .done(DONE),
    .ld(ld),
    .shift(shift),
    .state(state),
    .newstate(newstate),
    .IDLE(IDLE),
    .b00(b00),
    .MUL(MUL),
    .b01(b01),
    .DONE(DONE),
    .b10(b10),
    .posedge(posedge)
);
