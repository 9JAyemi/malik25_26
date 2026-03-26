module duration_lut_sva (
    input logic        clk,
    input logic [3:0]  lookup,
    input logic [15:0] duration
);

    localparam logic [15:0]
        BREVE            = 16'd48000,
        SEMIBREVE        = 16'd24000,
        DOTTED_MINIM     = 16'd18000,
        MINIM            = 16'd12000,
        DOTTED_CROTCHET  = 16'd9000,
        CROTCHET         = 16'd6000,
        DOTTED_QUAVER    = 16'd4500,
        QUAVER           = 16'd3000,
        TUPLET           = 16'd2000,
        SEMIQUAVER       = 16'd1500,
        UNDEF            = 16'd1000;

    // lookup 0 returns UNDEF.
    check_lookup_0_maps_undef: assert property (
        @(posedge clk) (lookup == 4'd0) |-> (duration == UNDEF)
    );

    // lookup 1 returns SEMIQUAVER.
    check_lookup_1_maps_semiquaver: assert property (
        @(posedge clk) (lookup == 4'd1) |-> (duration == SEMIQUAVER)
    );

    // lookup 2 returns TUPLET.
    check_lookup_2_maps_tuplet: assert property (
        @(posedge clk) (lookup == 4'd2) |-> (duration == TUPLET)
    );

    // lookup 3 returns QUAVER.
    check_lookup_3_maps_quaver: assert property (
        @(posedge clk) (lookup == 4'd3) |-> (duration == QUAVER)
    );

    // lookup 4 returns DOTTED_QUAVER.
    check_lookup_4_maps_dotted_quaver: assert property (
        @(posedge clk) (lookup == 4'd4) |-> (duration == DOTTED_QUAVER)
    );

    // lookup 5 returns CROTCHET.
    check_lookup_5_maps_crotchet: assert property (
        @(posedge clk) (lookup == 4'd5) |-> (duration == CROTCHET)
    );

    // lookup 6 returns DOTTED_CROTCHET.
    check_lookup_6_maps_dotted_crotchet: assert property (
        @(posedge clk) (lookup == 4'd6) |-> (duration == DOTTED_CROTCHET)
    );

    // lookup 7 returns MINIM.
    check_lookup_7_maps_minim: assert property (
        @(posedge clk) (lookup == 4'd7) |-> (duration == MINIM)
    );

    // lookup 8 returns DOTTED_MINIM.
    check_lookup_8_maps_dotted_minim: assert property (
        @(posedge clk) (lookup == 4'd8) |-> (duration == DOTTED_MINIM)
    );

    // lookup 9 returns SEMIBREVE.
    check_lookup_9_maps_semibreve: assert property (
        @(posedge clk) (lookup == 4'd9) |-> (duration == SEMIBREVE)
    );

    // lookup 10 returns BREVE.
    check_lookup_10_maps_breve: assert property (
        @(posedge clk) (lookup == 4'd10) |-> (duration == BREVE)
    );

    // lookup 11 through 15 return UNDEF.
    check_lookup_11_to_15_maps_undef: assert property (
        @(posedge clk) (lookup >= 4'd11) |-> (duration == UNDEF)
    );

endmodule