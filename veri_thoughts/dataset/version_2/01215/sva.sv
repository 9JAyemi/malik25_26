module nova_io_pio_dummy_sva (
    input logic        pclk,
    input logic        bs_rst,     // Active-low async reset
    input logic        bs_stb,
    input logic        bs_we,
    input logic [7:0]  bs_adr,
    input logic [15:0] bs_din,
    input logic [15:0] bs_dout,
    input logic        r_DONE,
    input logic        r_BUSY
);
    parameter logic [5:0] device_addr = 6'b000000;

    // During reset, flags and bs_dout drive known values.
    reset_known_values: assert property (
        @(posedge pclk) !bs_rst |-> (r_DONE == 1'b1) && (r_BUSY == 1'b0) && (bs_dout == {1'b0, 1'b1, 14'h0000})
    );

    // bs_dout must reflect r_BUSY and r_DONE with lower 14 bits zero.
    dout_reflects_flags: assert property (
        @(posedge pclk) disable iff (!bs_rst) (bs_dout == {r_BUSY, r_DONE, 14'h0000})
    );

    // Write to group 00 with cmd 01 drives DONE=0, BUSY=1 on next cycle.
    write_cmd01_sets_busy: assert property (
        @(posedge pclk) disable iff (!bs_rst)
            (bs_stb && (bs_adr[5:0] == device_addr) && bs_we && (bs_adr[7:6] == 2'b00) && (bs_din[15:14] == 2'b01))
            |=> (r_DONE == 1'b0) && (r_BUSY == 1'b1)
    );

    // Write to group 00 with cmd 10 drives DONE=0, BUSY=0 on next cycle.
    write_cmd10_clears_busy_and_done: assert property (
        @(posedge pclk) disable iff (!bs_rst)
            (bs_stb && (bs_adr[5:0] == device_addr) && bs_we && (bs_adr[7:6] == 2'b00) && (bs_din[15:14] == 2'b10))
            |=> (r_DONE == 1'b0) && (r_BUSY == 1'b0)
    );

    // Write to group 00 with cmd 11 does not change flags.
    write_cmd11_no_change: assert property (
        @(posedge pclk) disable iff (!bs_rst)
            (bs_stb && (bs_adr[5:0] == device_addr) && bs_we && (bs_adr[7:6] == 2'b00) && (bs_din[15:14] == 2'b11))
            |=> (r_DONE == $past(r_DONE)) && (r_BUSY == $past(r_BUSY))
    );

    // Write to group 00 with cmd 00 does not change flags.
    write_cmd00_no_change: assert property (
        @(posedge pclk) disable iff (!bs_rst)
            (bs_stb && (bs_adr[5:0] == device_addr) && bs_we && (bs_adr[7:6] == 2'b00) && (bs_din[15:14] == 2'b00))
            |=> (r_DONE == $past(r_DONE)) && (r_BUSY == $past(r_BUSY))
    );

    // Writes to groups 01/10/11 do not change flags.
    write_group_non00_no_change: assert property (
        @(posedge pclk) disable iff (!bs_rst)
            (bs_stb && (bs_adr[5:0] == device_addr) && bs_we && (bs_adr[7:6] != 2'b00))
            |=> (r_DONE == $past(r_DONE)) && (r_BUSY == $past(r_BUSY))
    );

    // Reads (any group) do not change flags.
    read_access_no_change: assert property (
        @(posedge pclk) disable iff (!bs_rst)
            (bs_stb && (bs_adr[5:0] == device_addr) && !bs_we)
            |=> (r_DONE == $past(r_DONE)) && (r_BUSY == $past(r_BUSY))
    );

    // Non-targeted accesses do not change flags.
    non_target_access_no_change: assert property (
        @(posedge pclk) disable iff (!bs_rst)
            (bs_stb && (bs_adr[5:0] != device_addr))
            |=> (r_DONE == $past(r_DONE)) && (r_BUSY == $past(r_BUSY))
    );

    // BUSY implies DONE is low.
    busy_implies_done_low: assert property (
        @(posedge pclk) disable iff (!bs_rst) r_BUSY |-> (r_DONE == 1'b0)
    );

endmodule