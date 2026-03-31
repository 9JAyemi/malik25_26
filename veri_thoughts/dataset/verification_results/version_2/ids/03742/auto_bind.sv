// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk_cntr, baud_rate, B300, b0, b1010001011000010100, B600, b0101000101100001010, B1200, b0010100010110000100, B2400, b0001010001011000010, B4800, b0000101000101100000, B9600, b0000010100010110000, B19200, b0000001010001010111, B38400, b0000000101000101011, B57600, b0000000011011000111, B115200, b0000000001101100011, check_reset_forces_default_baud, assert, property, posedge, check_baud_0_maps_to_b300, disable, iff, h0, check_baud_1_maps_to_b600, h1, check_baud_2_maps_to_b1200, h2, check_baud_3_maps_to_b2400, h3, check_baud_4_maps_to_b4800, h4, check_baud_5_maps_to_b9600, h5, check_baud_6_maps_to_b19200, h6, check_baud_7_maps_to_b38400, h7, check_baud_8_maps_to_b57600, h8, check_baud_9_maps_to_b115200, h9, check_baud_default_maps_to_b9600, check_reset_clears_counter_and_output, d0, check_counter_advances_and_output_holds, past, d1, check_terminal_count_resets_and_toggles
bind clk_div clk_div_sva auto_sva_inst (
    .CLKIN(CLKIN),
    .RST(RST),
    .BAUD(BAUD),
    .CLKOUT(CLKOUT)
);
