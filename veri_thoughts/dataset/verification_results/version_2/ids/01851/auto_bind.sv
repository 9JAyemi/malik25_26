// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): data_reg, sel_inv, check_reset_forces_zero, assert, property, posedge, b000, b0, check_reset_holds_zero_next, check_data_reg_holds_when_disabled, disable, iff, stable, check_out_holds_when_disabled, check_data_reg_load_on_enable, past, check_out_update_sel1, check_out_update_sel0, check_sel_inv_complement
bind mux3to1_async_reset_ce mux3to1_async_reset_ce_sva auto_sva_inst (
    .data_in(data_in),
    .sel(sel),
    .clk(clk),
    .reset(reset),
    .enable(enable),
    .out(out)
);
