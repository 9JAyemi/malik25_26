// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_cs_onehot0, assert, property, posedge, disable, iff, onehot0, check_cs_decode_63, h63, b10000000, check_cs_decode_64, h64, b01000000, check_cs_decode_65, h65, b00100000, check_cs_decode_66, h66, b00010000, check_cs_decode_67, h67, b00001000, check_cs_decode_68, h68, b00000100, check_cs_decode_69, h69, b00000010, check_cs_decode_70, h70, b00000001, check_cs_decode_default, b00000000, check_mux_altavoz, check_mux_ultra, check_mux_audio, check_mux_bt, check_mux_mult, check_mux_div, check_mux_uart, b0, check_mux_dp_ram, check_mux_default, h0000
bind j1_peripheral_mux j1_peripheral_mux_sva auto_sva_inst (
    .sys_clk_i(sys_clk_i),
    .sys_rst_i(sys_rst_i),
    .j1_io_rd(j1_io_rd),
    .j1_io_wr(j1_io_wr),
    .j1_io_addr(j1_io_addr),
    .j1_io_din(j1_io_din),
    .cs(cs),
    .mult_dout(mult_dout),
    .div_dout(div_dout),
    .uart_dout(uart_dout),
    .dp_ram_dout(dp_ram_dout),
    .bt_dout(bt_dout),
    .audio_dout(audio_dout),
    .ultra_dout(ultra_dout),
    .echo(echo)
);
