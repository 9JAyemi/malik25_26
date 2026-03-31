// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): DEVOPTIONS, h0E, DEVOPTS2, h0F, reset_clears_all_control_outputs, assert, property, posedge, b0, write_devoptions_updates_outputs, disable, iff, b1, past, write_devopts2_updates_outputs, write_devoptions_preserves_devopts2_outputs, write_devopts2_preserves_devoptions_outputs, no_targeted_write_holds_outputs, no_read_returns_default_bus, hFF, read_unknown_address_returns_default_bus, read_devoptions_returns_current_value, read_devopts2_returns_current_low_bits, write_then_read_devopts2_returns_written_byte
bind control_enable_options control_enable_options_sva auto_sva_inst (
    .clk(clk),
    .rst_n(rst_n),
    .zxuno_addr(zxuno_addr),
    .zxuno_regrd(zxuno_regrd),
    .zxuno_regwr(zxuno_regwr),
    .din(din),
    .dout(dout),
    .oe_n(oe_n),
    .disable_ay(disable_ay),
    .disable_turboay(disable_turboay),
    .disable_7ffd(disable_7ffd),
    .disable_1ffd(disable_1ffd),
    .disable_romsel7f(disable_romsel7f),
    .disable_romsel1f(disable_romsel1f),
    .enable_timexmmu(enable_timexmmu),
    .disable_spisd(disable_spisd),
    .disable_timexscr(disable_timexscr),
    .disable_ulaplus(disable_ulaplus),
    .disable_radas(disable_radas)
);
