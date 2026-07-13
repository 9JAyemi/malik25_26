// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_binary_reg1_captures_binary_in_on_rstn, assert, property, posedge, disable, iff, b1, binary_reg1, past, check_binary_reg2_captures_binary_reg1_on_rstn, binary_reg2, check_gray_reg1_captures_gray_out_on_rstn, gray_reg1, check_gray_reg2_captures_gray_reg1_on_rstn, gray_reg2, check_gray_out_update_on_gray_ctrl, b0, check_gray_out_bit0_on_gray_ctrl, check_gray_out_bit1_on_gray_ctrl, check_gray_out_bit2_on_gray_ctrl, check_gray_out_bit3_on_gray_ctrl
bind gray_converter gray_converter_sva auto_sva_inst (
    .binary_in(binary_in),
    .gray_ctrl(gray_ctrl),
    .rst_n(rst_n),
    .gray_out(gray_out)
);
