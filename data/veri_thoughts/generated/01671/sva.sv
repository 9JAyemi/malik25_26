module sbox64_sva (
    input logic clk,
    input logic [5:0] addr,
    input logic [3:0] dout
);
    ///// S-box mapping checks /////
    // addr 0x00 maps to 0xE.
    check_map_00: assert property (
        @(posedge clk) (addr == 6'h00) |-> (dout == 4'h0E)
    );
    // addr 0x01 maps to 0x4.
    check_map_01: assert property (
        @(posedge clk) (addr == 6'h01) |-> (dout == 4'h04)
    );
    // addr 0x02 maps to 0xD.
    check_map_02: assert property (
        @(posedge clk) (addr == 6'h02) |-> (dout == 4'h0D)
    );
    // addr 0x03 maps to 0x1.
    check_map_03: assert property (
        @(posedge clk) (addr == 6'h03) |-> (dout == 4'h01)
    );
    // addr 0x04 maps to 0x2.
    check_map_04: assert property (
        @(posedge clk) (addr == 6'h04) |-> (dout == 4'h02)
    );
    // addr 0x05 maps to 0xF.
    check_map_05: assert property (
        @(posedge clk) (addr == 6'h05) |-> (dout == 4'h0F)
    );
    // addr 0x06 maps to 0xB.
    check_map_06: assert property (
        @(posedge clk) (addr == 6'h06) |-> (dout == 4'h0B)
    );
    // addr 0x07 maps to 0x8.
    check_map_07: assert property (
        @(posedge clk) (addr == 6'h07) |-> (dout == 4'h08)
    );
    // addr 0x08 maps to 0x3.
    check_map_08: assert property (
        @(posedge clk) (addr == 6'h08) |-> (dout == 4'h03)
    );
    // addr 0x09 maps to 0xA.
    check_map_09: assert property (
        @(posedge clk) (addr == 6'h09) |-> (dout == 4'h0A)
    );
    // addr 0x0A maps to 0x6.
    check_map_0A: assert property (
        @(posedge clk) (addr == 6'h0A) |-> (dout == 4'h06)
    );
    // addr 0x0B maps to 0xC.
    check_map_0B: assert property (
        @(posedge clk) (addr == 6'h0B) |-> (dout == 4'h0C)
    );
    // addr 0x0C maps to 0x5.
    check_map_0C: assert property (
        @(posedge clk) (addr == 6'h0C) |-> (dout == 4'h05)
    );
    // addr 0x0D maps to 0x9.
    check_map_0D: assert property (
        @(posedge clk) (addr == 6'h0D) |-> (dout == 4'h09)
    );
    // addr 0x0E maps to 0x0.
    check_map_0E: assert property (
        @(posedge clk) (addr == 6'h0E) |-> (dout == 4'h00)
    );
    // addr 0x0F maps to 0x7.
    check_map_0F: assert property (
        @(posedge clk) (addr == 6'h0F) |-> (dout == 4'h07)
    );
    // All other addresses (0x10..0x3F) map to 0x0 (default).
    check_map_default: assert property (
        @(posedge clk) (addr >= 6'h10) |-> (dout == 4'h00)
    );

    ///// Functional sanity /////
    // If addr is stable across cycles, dout is stable (pure combinational function).
    check_stable_when_addr_stable: assert property (
        @(posedge clk) $stable(addr) |-> $stable(dout)
    );
endmodule