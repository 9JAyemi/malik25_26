// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): state_reg, counter, idle, b00, leer, b01, fin, b10, check_reset_release_defaults, assert, property, posedge, disable, iff, fell, d0, b0, check_state_encoding_valid, inside, check_idle_stay_when_btn0, check_idle_to_leer_when_btn1, b1, check_leer_to_fin, check_fin_to_idle, check_wea_const_zero, check_addra_inc_in_fin, past, check_addra_hold_in_idle, check_addra_hold_in_leer, check_counter_inc_in_leer, check_counter_hold_in_idle, check_counter_reset_in_fin_at_15, b1111, check_counter_hold_in_fin_not_15
bind bram_controller bram_controller_sva auto_sva_inst (
    .clk(clk),
    .reset(reset),
    .btn(btn),
    .wea(wea),
    .addra(addra)
);
