// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_state_register_updates_from_next, assert, property, isunknown, past, check_s0_in0_go_s1, check_s1_in0_go_s2, check_s2_in0_go_s3, check_s3_in0_go_s4, check_s4_in0_go_s5, check_in1_forces_s5_from_any, b1, inside, check_s5_absorbing, check_out_matches_state, check_out_sticky_when_high
bind fsm fsm_sva auto_sva_inst (
    .clk(clk),
    .in(in),
    .out(out),
    .currentState(currentState),
    .nextState(nextState),
    .s0(s0),
    .b000(b000),
    .s1(s1),
    .b001(b001),
    .s2(s2),
    .b010(b010),
    .s3(s3),
    .b011(b011),
    .s4(s4),
    .b100(b100),
    .s5(s5),
    .b101(b101),
    .posedge(posedge),
    .b0(b0)
);
