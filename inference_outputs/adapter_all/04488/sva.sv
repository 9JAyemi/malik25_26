module bcd_converter_sva (
    input logic [3:0] D,
    input logic [7:0] BCD
);

    // D=0 maps to BCD=0x00.
    check_map_d0: assert property (
        @($global_clock) (D == 4'h0) |-> (BCD == 8'h00)
    );

    // D=1 maps to BCD=0x01.
    check_map_d1: assert property (
        @($global_clock) (D == 4'h1) |-> (BCD == 8'h01)
    );

    // D=2 maps to BCD=0x02.
    check_map_d2: assert property (
        @($global_clock) (D == 4'h2) |-> (BCD == 8'h02)
    );

    // D=3 maps to BCD=0x03.
    check_map_d3: assert property (
        @($global_clock) (D == 4'h3) |-> (BCD == 8'h03)
    );

    // D=4 maps to BCD=0x04.
    check_map_d4: assert property (
        @($global_clock) (D == 4'h4) |-> (BCD == 8'h04)
    );

    // D=5 maps to BCD=0x05.
    check_map_d5: assert property (
        @($global_clock) (D == 4'h5) |-> (BCD == 8'h05)
    );

    // D=6 maps to BCD=0x06.
    check_map_d6: assert property (
        @($global_clock) (D == 4'h6) |-> (BCD == 8'h06)
    );

    // D=7 maps to BCD=0x07.
    check_map_d7: assert property (
        @($global_clock) (D == 4'h7) |-> (BCD == 8'h07)
    );

    // D=8 maps to BCD=0x08.
    check_map_d8: assert property (
        @($global_clock) (D == 4'h8) |-> (BCD == 8'h08)
    );

    // D=9 maps to BCD=0x09.
    check_map_d9: assert property (
        @($global_clock) (D == 4'h9) |-> (BCD == 8'h09)
    );

    // D=A maps to BCD=0x10.
    check_map_da: assert property (
        @($global_clock) (D == 4'hA) |-> (BCD == 8'h10)
    );

    // D=B maps to BCD=0x11.
    check_map_db: assert property (
        @($global_clock) (D == 4'hB) |-> (BCD == 8'h11)
    );

    // D=C maps to BCD=0x12.
    check_map_dc: assert property (
        @($global_clock) (D == 4'hC) |-> (BCD == 8'h12)
    );

    // D=D maps to BCD=0x13.
    check_map_dd: assert property (
        @($global_clock) (D == 4'hD) |-> (BCD == 8'h13)
    );

    // D=E maps to BCD=0x14.
    check_map_de: assert property (
        @($global_clock) (D == 4'hE) |-> (BCD == 8'h14)
    );

    // D=F maps to BCD=0x15.
    check_map_df: assert property (
        @($global_clock) (D == 4'hF) |-> (BCD == 8'h15)
    );

    // BCD upper nibble is always zero.
    check_bcd_upper_zero: assert property (
        @($global_clock) (BCD[7:4] == 4'h0)
    );

    // BCD lower nibble matches the input nibble.
    check_bcd_lower_matches_input: assert property (
        @($global_clock) (BCD[3:0] == D)
    );

endmodule