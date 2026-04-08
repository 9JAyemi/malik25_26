// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): LEFT, d160, RIGHT, d480, TILE_W, d32, BOTTOM, TILE_H, d16, check_sel_col_decode, assert, property, posedge, check_sel_row_decode, check_out_zero_outside_window, b0000, check_block_zero_blank, b000, check_narrow_center_border, b0, d8, d23, d0, d15, b1000, check_narrow_center_fill_block_001, b001, b1100, check_narrow_center_fill_block_010, b010, b1011, check_narrow_center_fill_block_011, b011, b1101, check_narrow_side_columns_border, check_narrow_outer_blank_non_011, b11, check_narrow_outer_block_011_border, d31, check_narrow_outer_block_011_fill, b1110, check_wide_border, b1, check_wide_fill_block_100, b100, b1001, check_wide_fill_block_101, b101, b1010, check_wide_fill_block_110, b110, check_wide_fill_block_111, b111, b1111
bind draw_block draw_block_assertions auto_sva_inst (
    .clock(clock),
    .vcounter(vcounter),
    .hcounter(hcounter),
    .block(block),
    .sel_row(sel_row),
    .sel_col(sel_col),
    .out(out)
);
