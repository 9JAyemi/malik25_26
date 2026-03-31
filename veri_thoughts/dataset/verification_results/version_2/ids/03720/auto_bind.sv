// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): state_reg, count, NSG, b00, NSG_YELLOW, b01, EWG, b10, EWG_YELLOW, b11, check_reset_state_nsg, assert, property, posedge, check_reset_outputs_nsg, b1, b0, check_nsg_outputs, disable, iff, check_nsg_yellow_outputs, check_ewg_outputs, check_ewg_yellow_outputs, check_nsg_timeout_transition, d30, d0, check_nsg_count_increment, past, d1, check_nsg_yellow_timeout_transition, d5, check_nsg_yellow_count_increment, check_ewg_timeout_transition, d20, check_ewg_count_increment, check_ewg_yellow_timeout_transition, check_ewg_yellow_count_increment
bind traffic_light_fsm traffic_light_fsm_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .NSG_LED(NSG_LED),
    .EWG_LED(EWG_LED),
    .yellow_LED(yellow_LED)
);
