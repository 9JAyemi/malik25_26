// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_reset_clears_out, assert, property, posedge, b0000, check_out_holds_without_read, disable, iff, past, check_read_sel_01_routes_mux_in_0, b01, check_read_sel_10_routes_mux_in_1, b10, check_read_sel_11_routes_mux_in_2, b11
bind top_module top_module_sva auto_sva_inst (
    .clk(clk),
    .rst_n(rst_n),
    .write_en(write_en),
    .write_addr(write_addr),
    .write_data(write_data),
    .read_en(read_en),
    .read_addr(read_addr),
    .mux_in_0(mux_in_0),
    .mux_in_1(mux_in_1),
    .mux_in_2(mux_in_2),
    .mux_in_3(mux_in_3),
    .mux_sel(mux_sel),
    .out(out)
);
