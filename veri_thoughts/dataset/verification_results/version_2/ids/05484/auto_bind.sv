// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_to_idle, assert, property, posedge, check_ctr_en_decode, disable, iff, check_ctr_ar_decode, check_idle_to_prerun_on_start, check_idle_stays_idle_without_start, check_prerun_to_stopped_on_stop, check_prerun_to_run_without_stop, check_run_to_stopped_on_stop, check_run_stays_run_without_stop, check_stopped_to_idle_on_start_deassert, check_stopped_stays_stopped_on_start_assert
bind ctr_fsm ctr_fsm_sva auto_sva_inst (
    .clk(clk),
    .ar(ar),
    .start(start),
    .stop(stop),
    .ctr_en(ctr_en),
    .ctr_ar(ctr_ar),
    .state(state),
    .IDLE(IDLE),
    .b00(b00),
    .PRERUN(PRERUN),
    .b01(b01),
    .RUN(RUN),
    .b10(b10),
    .STOPPED(STOPPED),
    .b11(b11),
    .start_assert(start_assert),
    .b1(b1),
    .stop_assert(stop_assert),
    .b0(b0)
);
