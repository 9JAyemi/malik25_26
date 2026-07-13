module bcd_converter_sva (
    input logic [3:0] D,
    input logic [7:0] BCD
);

    // Purely combinational RTL with no explicit clock or reset; sample on Jasper global clock.

    // D=0 maps to BCD 00.
    check_d0_maps_to_bcd00: assert property (
        @($global_clock) (D == 4'h0) |-> (BCD == 8'h00)
    );

    // D=1 maps to BCD 01.
    check_d1_maps_to_bcd01: assert property (
        @($global_clock) (D == 4'h1) |-> (BCD == 8'h01)
    );

    // D=2 maps to BCD 02.
    check_d2_maps_to_bcd02: assert property (
        @($global_clock) (D == 4'h2) |-> (BCD == 8'h02)
    );

    // D=3 maps to BCD 03.
    check_d3_maps_to_bcd03: assert property (
        @($global_clock) (D == 4'h3) |-> (BCD == 8'h03)
    );

    // D=4 maps to BCD 04.
    check_d4_maps_to_bcd04: assert property (
        @($global_clock) (D == 4'h4) |-> (BCD == 8'h04)
    );

    // D=5 maps to BCD 05.
    check_d5_maps_to_bcd05: assert property (
        @($global_clock) (D == 4'h5) |-> (BCD == 8'h05)
    );

    // D=6 maps to BCD 06.
    check_d6_maps_to_bcd06: assert property (
        @($global_clock) (D == 4'h6) |-> (BCD == 8'h06)
    );

    // D=7 maps to BCD 07.
    check_d7_maps_to_bcd07: assert property (
        @($global_clock) (D == 4'h7) |-> (BCD == 8'h07)
    );

    // D=8 maps to BCD 08.
    check_d8_maps_to_bcd08: assert property (
        @($global_clock) (D == 4'h8) |-> (BCD == 8'h08)
    );

    // D=9 maps to BCD 09.
    check_d9_maps_to_bcd09: assert property (
        @($global_clock) (D == 4'h9) |-> (BCD == 8'h09)
    );

    // D=10 maps to BCD 10.
    check_d10_maps_to_bcd10: assert property (
        @($global_clock) (D == 4'hA) |-> (BCD == 8'h10)
    );

    // D=11 maps to BCD 11.
    check_d11_maps_to_bcd11: assert property (
        @($global_clock) (D == 4'hB) |-> (BCD == 8'h11)
    );

    // D=12 maps to BCD 12.
    check_d12_maps_to_bcd12: assert property (
        @($global_clock) (D == 4'hC) |-> (BCD == 8'h12)
    );

    // D=13 maps to BCD 13.
    check_d13_maps_to_bcd13: assert property (
        @($global_clock) (D == 4'hD) |-> (BCD == 8'h13)
    );

    // D=14 maps to BCD 14.
    check_d14_maps_to_bcd14: assert property (
        @($global_clock) (D == 4'hE) |-> (BCD == 8'h14)
    );

    // D=15 maps to BCD 15.
    check_d15_maps_to_bcd15: assert property (
        @($global_clock) (D == 4'hF) |-> (BCD == 8'h15)
    );

endmodule