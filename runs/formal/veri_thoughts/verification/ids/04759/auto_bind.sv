// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_output, assert, property, b0, check_hold_when_not_loading, disable, iff, past, check_full_left_shift, check_full_right_shift, check_modulo_left_shift, check_modulo_right_shift
bind Barrel_Shifter Barrel_Shifter_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .load_i(load_i),
    .Shift_Value_i(Shift_Value_i),
    .Shift_Data_i(Shift_Data_i),
    .Left_Right_i(Left_Right_i),
    .Bit_Shift_i(Bit_Shift_i),
    .N_mant_o(N_mant_o),
    .posedge(posedge)
);
