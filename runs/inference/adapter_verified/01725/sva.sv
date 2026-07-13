module mm_sva (
    input logic        clk,
    input logic [31:0] addr,
    input logic [7:0]  mod,
    input logic [31:0] eff_addr
);

// mod must match the RTL's full conditional expression.
    check_mod_full_mapping: assert property (
        @(posedge clk)
        mod == ((addr[31:20] == 12'h000) ? 8'h00 :
                (addr[31:24] ==  8'h10) ? 8'h01 :
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

// mod 0x01 only occurs for addresses with upper bits 10xxxxxx.
    check_mod_01_mapping: assert property (
        @(posedge clk)
        (mod == 8'h01) == (addr[31:24] == 8'h10)
    );

// mod 0x02 only occurs for addresses with upper bits f00xxx.
    check_mod_02_mapping: assert property (
        @(posedge clk)
        (mod == 8'h02) == (addr[31:20] == 12'hf00)
    );

// mod 0x03 only occurs for addresses with upper bits f01xxx.
    check_mod_03_mapping: assert property (
        @(posedge clk)
        (mod == 8'h03) == (addr[31:20] == 12'hf01)
    );

// mod 0x04 only occurs for addresses with upper bits f02xxx.
    check_mod_04_mapping: assert property (
        @(posedge clk)
        (mod == 8'h04) == (addr[31:20] == 12'hf02)
    );

// mod 0x05 only occurs for addresses with upper bits f03xxx.
    check_mod_05_mapping: assert property (
        @(posedge clk)
        (mod == 8'h05) == (addr[31:20] == 12'hf03)
    );

// mod 0x06 only occurs for addresses with upper bits f04xxx.
    check_mod_06_mapping: assert property (
        @(posedge clk)
        (mod == 8'h06) == (addr[31:20] == 12'hf04)
    );

// mod 0x07 only occurs for addresses with upper bits f05xxx.
    check_mod_07_mapping: assert property (
        @(posedge clk)
        (mod == 8'h07) == (addr[31:20] == 12'hf05)
    );

// mod 0x08 only occurs for addresses with upper bits f06xxx.
    check_mod_08_mapping: assert property (
        @(posedge clk)
        (mod == 8'h08) == (addr[31:20] == 12'hf06)
    );

// mod 0x0a only occurs for addresses with upper bits f07xxx.
    check_mod_0a_mapping: assert property (
        @(posedge clk)
        (mod == 8'h0a) == (addr[31:20] == 12'hf07)
    );

// mod 0x0b only occurs for addresses with upper bits f08xxx.
    check_mod_0b_mapping: assert property (
        @(posedge clk)
        (mod == 8'h0b) == (addr[31:20] == 12'hf08)
    );

// mod 0x09 only occurs for addresses with upper bits f0axxx.
    check_mod_09_mapping: assert property (
        @(posedge clk)
        (mod == 8'h09) == (addr[31:20] == 12'hf0a)
    );

// mod 0x00 occurs for all other address patterns.
    check_mod_00_default: assert property (
        @(posedge clk)
        (mod == 8'h00) == !((addr[31:20] == 12'h000) ||
                            (addr[31:24] ==  8'h10) ||
                            (addr[31:20] == 12'hf00) ||
                            (addr[31:20] == 12'hf01) ||
                            (addr[31:20] == 12'hf02) ||
                            (addr[31:20] == 12'hf03) ||
                            (addr[31:20] == 12'hf04) ||
                            (addr[31:20] == 12'hf05) ||
                            (addr[31:20] == 12'hf06) ||
                            (addr[31:20] == 12'hf07) ||
                            (addr[31:20] == 12'hf08) ||
                            (addr[31:20] == 12'hf0a))
    );

// eff_addr must match the RTL's full conditional expression.
    check_eff_addr_full_mapping: assert property (
        @(posedge clk)
        eff_addr == ((mod == 8'h01) ? {8'h00, addr[23:0]} : {12'h000, addr[19:0]})
    );

// For mod 0x01, eff_addr must have upper bits 00 and lower 24 bits of addr.
    check_eff_addr_mod_01: assert property (
        @(posedge clk)
        (mod == 8'h01) |-> (eff_addr == {8'h00, addr[23:0]})
    );

// For all other mods, eff_addr must have upper bits 000 and lower 20 bits of addr.
    check_eff_addr_other_mods: assert property (
        @(posedge clk)
        (mod != 8'h01) |-> (eff_addr == {12'h000, addr[19:0]})
    );

endmodule
