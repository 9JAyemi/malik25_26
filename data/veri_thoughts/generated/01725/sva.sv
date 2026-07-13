module mm_sva (
    input logic clk,
    input logic rst_n,
    input logic [31:0] addr,
    input logic [7:0] mod,
    input logic [31:0] eff_addr
);
    // mod must equal the decode function of addr
    check_mod_decode_function: assert property (
        @(posedge clk) disable iff (!rst_n)
        mod == (
            (addr[31:20] == 12'h000) ? 8'h00 :
            (addr[31:24] ==   8'h10) ? 8'h01 :
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
                                       8'h00
        )
    );

    // mod takes only values produced by the decode
    check_mod_value_set: assert property (
        @(posedge clk) disable iff (!rst_n)
        mod inside {8'h00,8'h01,8'h02,8'h03,8'h04,8'h05,8'h06,8'h07,8'h08,8'h09,8'h0a,8'h0b}
    );

    // If addr[31:20]==0x000 then mod==0
    decode_000_to_0: assert property (
        @(posedge clk) disable iff (!rst_n)
        (addr[31:20] == 12'h000) |-> (mod == 8'h00)
    );

    // If addr[31:24]==0x10 then mod==1
    decode_10_to_1: assert property (
        @(posedge clk) disable iff (!rst_n)
        (addr[31:24] == 8'h10) |-> (mod == 8'h01)
    );

    // If addr[31:20]==0xf00 then mod==2
    decode_f00_to_2: assert property (
        @(posedge clk) disable iff (!rst_n)
        (addr[31:20] == 12'hf00) |-> (mod == 8'h02)
    );

    // If addr[31:20]==0xf06 then mod==8
    decode_f06_to_8: assert property (
        @(posedge clk) disable iff (!rst_n)
        (addr[31:20] == 12'hf06) |-> (mod == 8'h08)
    );

    // If addr[31:20]==0xf07 then mod==10
    decode_f07_to_10: assert property (
        @(posedge clk) disable iff (!rst_n)
        (addr[31:20] == 12'hf07) |-> (mod == 8'h0a)
    );

    // If addr[31:20]==0xf08 then mod==11
    decode_f08_to_11: assert property (
        @(posedge clk) disable iff (!rst_n)
        (addr[31:20] == 12'hf08) |-> (mod == 8'h0b)
    );

    // If addr[31:20]==0xf0a then mod==9
    decode_f0a_to_9: assert property (
        @(posedge clk) disable iff (!rst_n)
        (addr[31:20] == 12'hf0a) |-> (mod == 8'h09)
    );

    // If no decode case matches, mod==0 (default)
    decode_default_to_0: assert property (
        @(posedge clk) disable iff (!rst_n)
        !(
            (addr[31:20] == 12'h000) ||
            (addr[31:24] == 8'h10)   ||
            (addr[31:20] inside {12'hf00,12'hf01,12'hf02,12'hf03,12'hf04,12'hf05,12'hf06,12'hf07,12'hf08,12'hf0a})
        ) |-> (mod == 8'h00)
    );

    // If mod==1 then addr[31:24]==0x10
    mod1_implies_10: assert property (
        @(posedge clk) disable iff (!rst_n)
        (mod == 8'h01) |-> (addr[31:24] == 8'h10)
    );

    // If mod==10 then addr[31:20]==0xf07
    mod10_implies_f07: assert property (
        @(posedge clk) disable iff (!rst_n)
        (mod == 8'h0a) |-> (addr[31:20] == 12'hf07)
    );

    // If mod==11 then addr[31:20]==0xf08
    mod11_implies_f08: assert property (
        @(posedge clk) disable iff (!rst_n)
        (mod == 8'h0b) |-> (addr[31:20] == 12'hf08)
    );

    // If mod==9 then addr[31:20]==0xf0a
    mod9_implies_f0a: assert property (
        @(posedge clk) disable iff (!rst_n)
        (mod == 8'h09) |-> (addr[31:20] == 12'hf0a)
    );

    // eff_addr must equal the function of mod and addr
    check_eff_addr_function: assert property (
        @(posedge clk) disable iff (!rst_n)
        eff_addr == ((mod == 8'h01) ? {8'h00, addr[23:0]} : {12'h000, addr[19:0]})
    );

    // When mod==1, eff_addr upper 8 bits are zero and low 24 mirror addr
    eff_addr_when_mod1: assert property (
        @(posedge clk) disable iff (!rst_n)
        (mod == 8'h01) |-> (eff_addr[31:24] == 8'h00) && (eff_addr[23:0] == addr[23:0])
    );

    // When mod!=1, eff_addr upper 12 bits are zero and low 20 mirror addr
    eff_addr_when_not_mod1: assert property (
        @(posedge clk) disable iff (!rst_n)
        (mod != 8'h01) |-> (eff_addr[31:20] == 12'h000) && (eff_addr[19:0] == addr[19:0])
    );
endmodule