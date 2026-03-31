module mm_sva (
    input logic [31:0] addr,
    input logic [7:0]  mod,
    input logic [31:0] eff_addr
);

    // mod must match the RTL decode table.
    check_mod_decode: assert property (
        @($global_clock)
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

    // eff_addr must match the RTL mux.
    check_eff_addr_mux: assert property (
        @($global_clock)
        eff_addr == ((mod == 8'h01) ? {8'h00, addr[23:0]} : {12'h000, addr[19:0]})
    );

    // mod 00000000 maps to 00.
    check_mod_00000000: assert property (
        @($global_clock)
        (addr[31:20] == 12'h000) |-> (mod == 8'h00)
    );

    // mod 00000100 maps to 01.
    check_mod_00000100: assert property (
        @($global_clock)
        (addr[31:24] == 8'h10) |-> (mod == 8'h01)
    );

    // mod f0000000 maps to 02.
    check_mod_f0000000: assert property (
        @($global_clock)
        (addr[31:20] == 12'hf00) |-> (mod == 8'h02)
    );

    // mod f0000001 maps to 03.
    check_mod_f0000001: assert property (
        @($global_clock)
        (addr[31:20] == 12'hf01) |-> (mod == 8'h03)
    );

    // mod f0000002 maps to 04.
    check_mod_f0000002: assert property (
        @($global_clock)
        (addr[31:20] == 12'hf02) |-> (mod == 8'h04)
    );

    // mod f0000003 maps to 05.
    check_mod_f0000003: assert property (
        @($global_clock)
        (addr[31:20] == 12'hf03) |-> (mod == 8'h05)
    );

    // mod f0000004 maps to 06.
    check_mod_f0000004: assert property (
        @($global_clock)
        (addr[31:20] == 12'hf04) |-> (mod == 8'h06)
    );

    // mod f0000005 maps to 07.
    check_mod_f0000005: assert property (
        @($global_clock)
        (addr[31:20] == 12'hf05) |-> (mod == 8'h07)
    );

    // mod f0000006 maps to 08.
    check_mod_f0000006: assert property (
        @($global_clock)
        (addr[31:20] == 12'hf06) |-> (mod == 8'h08)
    );

    // mod f0000007 maps to 0a.
    check_mod_f0000007: assert property (
        @($global_clock)
        (addr[31:20] == 12'hf07) |-> (mod == 8'h0a)
    );

    // mod f0000008 maps to 0b.
    check_mod_f0000008: assert property (
        @($global_clock)
        (addr[31:20] == 12'hf08) |-> (mod == 8'h0b)
    );

    // mod f000000a maps to 09.
    check_mod_f000000a: assert property (
        @($global_clock)
        (addr[31:20] == 12'hf0a) |-> (mod == 8'h09)
    );

    // mod 00000001 through 00000009 map to 00.
    check_mod_default_00: assert property (
        @($global_clock)
        ((addr[31:20] != 12'h000) &&
         (addr[31:24] != 8'h10)  &&
         (addr[31:20] != 12'hf00) &&
         (addr[31:20] != 12'hf01) &&
         (addr[31:20] != 12'hf02) &&
         (addr[31:20] != 12'hf03) &&
         (addr[31:20] != 12'hf04) &&
         (addr[31:20] != 12'hf05) &&
         (addr[31:20] != 12'hf06) &&
         (addr[31:20] != 12'hf07) &&
         (addr[31:20] != 12'hf08) &&
         (addr[31:20] != 12'hf0a)) |-> (mod == 8'h00)
    );

    // eff_addr must be zero-extended when mod is 01.
    check_eff_addr_mod01_zero_extend: assert property (
        @($global_clock)
        (mod == 8'h01) |-> (eff_addr[31:24] == 8'h00)
    );

    // eff_addr must match addr[23:0] when mod is 01.
    check_eff_addr_mod01_low24: assert property (
        @($global_clock)
        (mod == 8'h01) |-> (eff_addr[23:0] == addr[23:0])
    );

    // eff_addr must be zero-extended when mod is not 01.
    check_eff_addr_not_mod01_zero_extend: assert property (
        @($global_clock)
        (mod != 8'h01) |-> (eff_addr[31:20] == 12'h000)
    );

    // eff_addr must match addr[19:0] when mod is not 01.
    check_eff_addr_not_mod01_low20: assert property (
        @($global_clock)
        (mod != 8'h01) |-> (eff_addr[19:0] == addr[19:0])
    );

endmodule