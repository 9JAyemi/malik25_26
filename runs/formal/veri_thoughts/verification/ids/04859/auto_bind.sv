// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): clk, check_memwrite_masks_all_bytes, assert, property, posedge, b0000, check_sw_shift_passthrough, b101011, check_sw_full_byte_enable, b1111, check_addr00_shift, b00, b0, check_addr00_byte_enable, b1000, check_addr01_shift, b01, check_addr01_byte_enable, b1100, check_addr10_shift, b10, check_addr10_byte_enable, b1110, check_addr11_shift_passthrough, b11, check_addr11_full_byte_enable
bind reg_shifter reg_shifter_sva auto_sva_inst (
    .rt_out(rt_out),
    .mem_addr_in(mem_addr_in),
    .MemWrite(MemWrite),
    .IR_out(IR_out),
    .rt_out_shift(rt_out_shift),
    .mem_byte_write_out(mem_byte_write_out)
);
