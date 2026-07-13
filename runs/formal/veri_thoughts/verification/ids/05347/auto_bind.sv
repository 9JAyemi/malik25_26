// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_flags_mutex, assert, property, posedge, disable, iff, check_idle_holds_flags, stable, check_simul_rw_holds_flags, check_empty_without_write_stays_empty, check_empty_write_only_clears_empty, check_full_without_read_stays_full, check_full_read_only_clears_full, check_empty_fall_requires_write_only, past, fell, check_full_fall_requires_read_only
bind flag_gen flag_gen_sva auto_sva_inst (
    .clk(clk),
    .rst(rst),
    .full(full),
    .emptyp(emptyp),
    .wr_en(wr_en),
    .rd_en(rd_en)
);
