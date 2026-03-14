module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W63_0_8_sva (
    input  logic        CLK,
    input  logic        EN,
    input  logic        TE,
    input  logic [62:0] ADD_W63_0_8,
    input  logic        ENCLK
);
    // ENCLK must equal mux of ADD_W63_0_8[0] and CLK selected by EN&TE.
    check_enclk_mux_function: assert property (
        @(posedge CLK) ENCLK == ((EN & TE) ? ADD_W63_0_8[0] : CLK)
    );

    // When enabled (EN&TE=1), ENCLK equals ADD_W63_0_8[0].
    check_selects_d_when_enabled: assert property (
        @(posedge CLK) (EN & TE) |-> (ENCLK == ADD_W63_0_8[0])
    );

    // When not enabled, ENCLK equals CLK.
    check_selects_clk_when_disabled: assert property (
        @(posedge CLK) !(EN & TE) |-> (ENCLK == CLK)
    );

    // If EN is LOW, ENCLK equals CLK.
    check_en_low_selects_clk: assert property (
        @(posedge CLK) (!EN) |-> (ENCLK == CLK)
    );

    // If TE is LOW, ENCLK equals CLK.
    check_te_low_selects_clk: assert property (
        @(posedge CLK) (!TE) |-> (ENCLK == CLK)
    );

    // If ENCLK differs from CLK, the D-path must be selected and ENCLK equals ADD_W63_0_8[0].
    check_enclk_differs_from_clk_only_when_enabled: assert property (
        @(posedge CLK) (ENCLK != CLK) |-> ((EN & TE) && (ENCLK == ADD_W63_0_8[0]))
    );

    // If ENCLK differs from ADD_W63_0_8[0], the CLK-path must be selected and ENCLK equals CLK.
    check_enclk_differs_from_d_only_when_disabled: assert property (
        @(posedge CLK) (ENCLK != ADD_W63_0_8[0]) |-> (!(EN & TE) && (ENCLK == CLK))
    );

    // At CLK posedge, if disabled, ENCLK must be HIGH (follows CLK).
    check_high_on_posedge_when_disabled: assert property (
        @(posedge CLK) (!(EN & TE)) |-> (ENCLK == 1'b1)
    );

    // When enabled across two cycles and ADD_W63_0_8[0] is stable, ENCLK stays stable.
    check_stable_when_enabled_and_d_stable: assert property (
        @(posedge CLK) ((EN & TE) && $past(EN & TE) && (ADD_W63_0_8[0] == $past(ADD_W63_0_8[0]))) |-> (ENCLK == $past(ENCLK))
    );

    // When enabled and ADD_W63_0_8[0] equals CLK, ENCLK equals CLK.
    check_enabled_equal_inputs_match: assert property (
        @(posedge CLK) ((EN & TE) && (ADD_W63_0_8[0] == CLK)) |-> (ENCLK == CLK)
    );
endmodule