module j1_peripheral_mux_sva(
    input logic        sys_clk_i,
    input logic        sys_rst_i,
    input logic        j1_io_rd,
    input logic        j1_io_wr,
    input logic [15:0] j1_io_addr,
    input logic [15:0] j1_io_din,
    input logic [7:0]  cs,
    input logic [15:0] mult_dout,
    input logic [15:0] div_dout,
    input logic        uart_dout,
    input logic [15:0] dp_ram_dout,
    input logic [15:0] bt_dout,
    input logic [15:0] audio_dout,
    input logic [15:0] ultra_dout,
    input logic        echo
);

    // The decoder only drives zero or a single chip-select bit.
    check_cs_onehot0: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        $onehot0(cs)
    );

    // Address 0x63 selects the altavoz chip-select bit.
    check_cs_decode_63: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        (j1_io_addr[15:8] == 8'h63) |-> (cs == 8'b10000000)
    );

    // Address 0x64 selects the ultra chip-select bit.
    check_cs_decode_64: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        (j1_io_addr[15:8] == 8'h64) |-> (cs == 8'b01000000)
    );

    // Address 0x65 selects the audio chip-select bit.
    check_cs_decode_65: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        (j1_io_addr[15:8] == 8'h65) |-> (cs == 8'b00100000)
    );

    // Address 0x66 selects the bt chip-select bit.
    check_cs_decode_66: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        (j1_io_addr[15:8] == 8'h66) |-> (cs == 8'b00010000)
    );

    // Address 0x67 selects the mult chip-select bit.
    check_cs_decode_67: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        (j1_io_addr[15:8] == 8'h67) |-> (cs == 8'b00001000)
    );

    // Address 0x68 selects the div chip-select bit.
    check_cs_decode_68: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        (j1_io_addr[15:8] == 8'h68) |-> (cs == 8'b00000100)
    );

    // Address 0x69 selects the uart chip-select bit.
    check_cs_decode_69: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        (j1_io_addr[15:8] == 8'h69) |-> (cs == 8'b00000010)
    );

    // Address 0x70 selects the dp_ram chip-select bit.
    check_cs_decode_70: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        (j1_io_addr[15:8] == 8'h70) |-> (cs == 8'b00000001)
    );

    // Unmapped addresses select no peripheral.
    check_cs_decode_default: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        ((j1_io_addr[15:8] != 8'h63) &&
         (j1_io_addr[15:8] != 8'h64) &&
         (j1_io_addr[15:8] != 8'h65) &&
         (j1_io_addr[15:8] != 8'h66) &&
         (j1_io_addr[15:8] != 8'h67) &&
         (j1_io_addr[15:8] != 8'h68) &&
         (j1_io_addr[15:8] != 8'h69) &&
         (j1_io_addr[15:8] != 8'h70)) |-> (cs == 8'b00000000)
    );

    // Altavoz select returns audio_dout.
    check_mux_altavoz: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        (cs == 8'b10000000) |-> (j1_io_din == audio_dout)
    );

    // Ultra select returns ultra_dout.
    check_mux_ultra: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        (cs == 8'b01000000) |-> (j1_io_din == ultra_dout)
    );

    // Audio select returns audio_dout.
    check_mux_audio: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        (cs == 8'b00100000) |-> (j1_io_din == audio_dout)
    );

    // BT select returns bt_dout.
    check_mux_bt: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        (cs == 8'b00010000) |-> (j1_io_din == bt_dout)
    );

    // Mult select returns mult_dout.
    check_mux_mult: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        (cs == 8'b00001000) |-> (j1_io_din == mult_dout)
    );

    // Div select returns div_dout.
    check_mux_div: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        (cs == 8'b00000100) |-> (j1_io_din == div_dout)
    );

    // UART select returns uart_dout zero-extended to 16 bits.
    check_mux_uart: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        (cs == 8'b00000010) |-> (j1_io_din == {15'b0, uart_dout})
    );

    // DP RAM select returns dp_ram_dout.
    check_mux_dp_ram: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        (cs == 8'b00000001) |-> (j1_io_din == dp_ram_dout)
    );

    // Any unmapped chip-select value returns zero data.
    check_mux_default: assert property (
        @(posedge sys_clk_i) disable iff (sys_rst_i)
        ((cs != 8'b10000000) &&
         (cs != 8'b01000000) &&
         (cs != 8'b00100000) &&
         (cs != 8'b00010000) &&
         (cs != 8'b00001000) &&
         (cs != 8'b00000100) &&
         (cs != 8'b00000010) &&
         (cs != 8'b00000001)) |-> (j1_io_din == 16'h0000)
    );

endmodule