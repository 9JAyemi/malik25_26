// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): check_driver_address_mux, assert, property, posedge, disable, iff, check_driver_read_mux, h0, check_driver_write_mux, check_driver_wdata_mux, check_hdd_readdata_mux, check_bios_readdata_mux, check_hdd_waitreq_zero, b0, check_bios_waitreq_zero, check_hdd_readdatavalid_reg, check_hdd_readdatavalid_blocked_in_reset, check_bios_addr_blocks_access_outside_window
bind to_driver_sd_avs to_driver_sd_avs_sva auto_sva_inst (
    .clk_sys(clk_sys),
    .rst(rst),
    .ao486_rst(ao486_rst),
    .hdd_avalon_master_address(hdd_avalon_master_address),
    .hdd_avalon_master_read(hdd_avalon_master_read),
    .hdd_avalon_master_readdata(hdd_avalon_master_readdata),
    .hdd_avalon_master_write(hdd_avalon_master_write),
    .hdd_avalon_master_writedata(hdd_avalon_master_writedata),
    .hdd_avalon_master_waitrequest(hdd_avalon_master_waitrequest),
    .hdd_avalon_master_readdatavalid(hdd_avalon_master_readdatavalid),
    .bios_loader_address(bios_loader_address),
    .bios_loader_read(bios_loader_read),
    .bios_loader_readdata(bios_loader_readdata),
    .bios_loader_write(bios_loader_write),
    .bios_loader_writedata(bios_loader_writedata),
    .bios_loader_waitrequest(bios_loader_waitrequest),
    .bios_loader_byteenable(bios_loader_byteenable),
    .driver_sd_avs_address(driver_sd_avs_address),
    .driver_sd_avs_read(driver_sd_avs_read),
    .driver_sd_avs_readdata(driver_sd_avs_readdata),
    .driver_sd_avs_write(driver_sd_avs_write),
    .driver_sd_avs_writedata(driver_sd_avs_writedata)
);
