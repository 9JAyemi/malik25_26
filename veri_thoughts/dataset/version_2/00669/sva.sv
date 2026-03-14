module to_driver_sd_avs_sva (
    input logic         clk_sys,
    input logic         rst,
    input logic         ao486_rst,

    input logic [31:0]  hdd_avalon_master_address,
    input logic         hdd_avalon_master_read,
    input logic [31:0]  hdd_avalon_master_readdata,
    input logic         hdd_avalon_master_write,
    input logic [31:0]  hdd_avalon_master_writedata,
    input logic         hdd_avalon_master_waitrequest,
    input logic         hdd_avalon_master_readdatavalid,

    input logic [31:0]  bios_loader_address,
    input logic         bios_loader_read,
    input logic [31:0]  bios_loader_readdata,
    input logic         bios_loader_write,
    input logic [31:0]  bios_loader_writedata,
    input logic         bios_loader_waitrequest,
    input logic [3:0]   bios_loader_byteenable,

    input logic [1:0]   driver_sd_avs_address,
    input logic         driver_sd_avs_read,
    input logic [31:0]  driver_sd_avs_readdata,
    input logic         driver_sd_avs_write,
    input logic [31:0]  driver_sd_avs_writedata
);

    ///// Path selection to driver_sd_avs /////
    // Address mux selects bits [3:2] from the active source.
    check_driver_address_mux: assert property (
        @(posedge clk_sys) disable iff (rst)
        driver_sd_avs_address == ((~ao486_rst) ? hdd_avalon_master_address[3:2] : bios_loader_address[3:2])
    );

    // Read control is from HDD when ~ao486_rst, else gated BIOS read in 0x0000_0000..0x0000_000F.
    check_driver_read_mux: assert property (
        @(posedge clk_sys) disable iff (rst)
        driver_sd_avs_read == ((~ao486_rst) ? hdd_avalon_master_read
                                            : (bios_loader_read && (bios_loader_address[31:4] == 28'h0)))
    );

    // Write control is from HDD when ~ao486_rst, else gated BIOS write in 0x0000_0000..0x0000_000F.
    check_driver_write_mux: assert property (
        @(posedge clk_sys) disable iff (rst)
        driver_sd_avs_write == ((~ao486_rst) ? hdd_avalon_master_write
                                             : (bios_loader_write && (bios_loader_address[31:4] == 28'h0)))
    );

    // Writedata is from the active source without additional gating.
    check_driver_wdata_mux: assert property (
        @(posedge clk_sys) disable iff (rst)
        driver_sd_avs_writedata == ((~ao486_rst) ? hdd_avalon_master_writedata : bios_loader_writedata)
    );

    ///// Return path to masters /////
    // HDD readdata reflects driver data when ~ao486_rst, else 0.
    check_hdd_readdata_mux: assert property (
        @(posedge clk_sys) disable iff (rst)
        hdd_avalon_master_readdata == ((~ao486_rst) ? driver_sd_avs_readdata : 32'h0)
    );

    // BIOS readdata reflects driver data when ao486_rst, else 0.
    check_bios_readdata_mux: assert property (
        @(posedge clk_sys) disable iff (rst)
        bios_loader_readdata == (ao486_rst ? driver_sd_avs_readdata : 32'h0)
    );

    // HDD waitrequest is hardwired LOW.
    check_hdd_waitreq_zero: assert property (
        @(posedge clk_sys) disable iff (rst)
        hdd_avalon_master_waitrequest == 1'b0
    );

    // BIOS waitrequest is hardwired LOW.
    check_bios_waitreq_zero: assert property (
        @(posedge clk_sys) disable iff (rst)
        bios_loader_waitrequest == 1'b0
    );

    ///// Registered status /////
    // HDD readdatavalid mirrors driver_sd_avs_read when ~ao486_rst, else 0.
    check_hdd_readdatavalid_reg: assert property (
        @(posedge clk_sys) disable iff (rst)
        hdd_avalon_master_readdatavalid == ((~ao486_rst) ? driver_sd_avs_read : 1'b0)
    );

    // HDD readdatavalid cannot be 1 while ao486_rst is asserted.
    check_hdd_readdatavalid_blocked_in_reset: assert property (
        @(posedge clk_sys) disable iff (rst)
        hdd_avalon_master_readdatavalid |-> (~ao486_rst)
    );

    ///// BIOS address gating /////
    // When BIOS address is outside 0x0000_0000..0x0000_000F, no read/write reaches the driver.
    check_bios_addr_blocks_access_outside_window: assert property (
        @(posedge clk_sys) disable iff (rst)
        ao486_rst && (bios_loader_address[31:4] != 28'h0) |-> (!driver_sd_avs_read && !driver_sd_avs_write)
    );

endmodule