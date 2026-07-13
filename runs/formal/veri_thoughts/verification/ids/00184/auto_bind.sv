// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): IDLE, b000, SEND, b001, WAIT1, b010, UPDATE1, b011, WAIT2, b100, UPDATE2, b101, check_reset_idle, assert, property, posedge, check_idle_to_send, disable, iff, check_send_to_wait1, check_wait1_to_update1, check_update1_to_wait2, check_wait2_to_update2, check_update2_to_idle, check_invalid_state_to_idle, check_next_state_is_legal, b1
bind state_machine state_machine_sva auto_sva_inst (
    .clk(clk),
    .rst_(rst_),
    .state_r(state_r)
);
