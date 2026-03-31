// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_lcd_rw_decode, assert, property, posedge, disable, iff, check_lcd_rs_decode, check_lcd_e_reset_low, b0, check_lcd_data_reset_zero, h00, check_lcd_e_set_on_access, b1, check_lcd_e_clear_without_access, check_lcd_data_capture_on_write, past, check_lcd_data_hold_without_write
bind NIOS_SYSTEMV3_LCD NIOS_SYSTEMV3_LCD_sva auto_sva_inst (
    .address(address),
    .begintransfer(begintransfer),
    .clk(clk),
    .read(read),
    .reset_n(reset_n),
    .write(write),
    .writedata(writedata),
    .LCD_E(LCD_E),
    .LCD_RS(LCD_RS),
    .LCD_RW(LCD_RW),
    .LCD_data(LCD_data)
);
