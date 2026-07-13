// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): eq_switch_decode, assert, property, posedge, h74, eq_bar_led_decode, h6C, eq_board_led_decode, h2F, eq_mem1_decode, b000, eq_mem2_decode, b101, at_most_one_active, onehot0, default_no_match_all_high, only_switch_on_0x74, only_bar_led_on_0x6C, only_board_led_on_0x2F
bind decoder decoder_sva auto_sva_inst (
    .address(address),
    .bar_led_ce_n(bar_led_ce_n),
    .board_led_ce_n(board_led_ce_n),
    .switch_ce_n(switch_ce_n),
    .mem1_ce_n(mem1_ce_n),
    .mem2_ce_n(mem2_ce_n)
);
