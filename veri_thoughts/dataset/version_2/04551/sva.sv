module addr_map_sva (
    input logic        clk,
    input logic [9:0]  hcount,
    input logic [9:0]  vcount,
    input logic [16:0] addr
);

    // addr must match the RTL continuous assignment.
    check_addr_equation: assert property (
        @(posedge clk)
        addr == ((vcount[9:1] << 8) + (vcount[9:1] << 6) + (hcount >> 1))
    );

    // The implemented expression only drives the low 10 bits of addr.
    check_addr_upper_bits_zero: assert property (
        @(posedge clk)
        addr[16:10] == 7'b0
    );

    // The low six addr bits come directly from hcount[6:1].
    check_addr_low_bits_from_hcount: assert property (
        @(posedge clk)
        addr[5:0] == hcount[6:1]
    );

    // Changing only hcount[0] must not change addr.
    check_addr_ignores_hcount_lsb: assert property (
        @(posedge clk)
        ($changed(hcount[0]) && $stable(hcount[9:1]) && $stable(vcount)) |-> $stable(addr)
    );

    // Changing only vcount[0] must not change addr.
    check_addr_ignores_vcount_lsb: assert property (
        @(posedge clk)
        ($changed(vcount[0]) && $stable(vcount[9:1]) && $stable(hcount)) |-> $stable(addr)
    );

    // Changing only vcount[9:4] must not change addr.
    check_addr_ignores_vcount_upper_bits: assert property (
        @(posedge clk)
        ($changed(vcount[9:4]) && $stable(vcount[3:0]) && $stable(hcount)) |-> $stable(addr)
    );

endmodule