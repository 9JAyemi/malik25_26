module mm_sva (
    input logic        clk,
    input logic [31:0] addr,
    input logic [7:0]  mod,
    input logic [31:0] eff_addr
);

    // mod must match the RTL address decode.
    check_mod_decode: assert property (
        @(posedge clk)
        mod == ((addr[31:20] == 12'h000) ? 8'h00 :
                (addr[31:24] == 8'h10)  ? 8'h01 :
                (addr[31:20] == 12'hf00) ? 8'h02 :
                (addr[31:20] == 12'hf01) ? 8'h03 :
                (addr[31:20] == 12'hf02) ? 8'h04 :
                (addr[31:20] == 12'hf03) ? 8'h05 :
                (addr[31:20] == 12'hf04) ? 8'h06 :
                (addr[31:20] == 12'hf05) ? 8'h07 :
                (addr[31:20] == 12'hf06) ? 8'h08 :
                (addr[31:20] == 12'hf07) ? 8'h0a :
                (addr[31:20] == 12'hf08) ? 8'h0b :
                (addr[31:20] == 12'hf0a) ? 8'h09 :
                                           8'h00)
    );

    // eff_addr must match the RTL address remap.
    check_eff_addr_map: assert property (
        @(posedge clk)
        eff_addr == ((mod == 8'h01) ? {8'h00, addr[23:0]} : {12'h000, addr[19:0]})
    );

    // mod 0x01 maps to the upper 24 address bits with zero extension.
    check_mod_01_mapping: assert property (
        @(posedge clk)
        (mod == 8'h01) |-> (eff_addr == {8'h00, addr[23:0]})
    );

    // All other mods map to the upper 20 address bits with zero extension.
    check_other_mod_mapping: assert property (
        @(posedge clk)
        (mod != 8'h01) |-> (eff_addr == {12'h000, addr[19:0]})
    );

    // eff_addr[19:0] is always the low 20 address bits.
    check_eff_addr_low20: assert property (
        @(posedge clk)
        eff_addr[19:0] == addr[19:0]
    );

    // eff_addr[31:20] is zero for all valid RTL address decodes.
    check_eff_addr_high12_zero: assert property (
        @(posedge clk)
        eff_addr[31:20] == 12'h000
    );

endmodule