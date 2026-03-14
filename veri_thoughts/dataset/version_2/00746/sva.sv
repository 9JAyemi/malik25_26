module SNPS_CLOCK_GATE_HIGH_RegisterAdd_W26_1_3_sva (
    input logic EN,
    input logic TE,
    input logic CLK,
    input logic ENCLK
);
    // Combinational gate: ENCLK = EN && TE && CLK; clock for assertions is CLK; no reset present.

    // ENCLK can only be HIGH when EN and TE are HIGH at the CLK posedge.
    check_enclk_only_when_en_te_high: assert property (
        @(posedge CLK) ENCLK |-> (EN && TE)
    );

    // When EN and TE are HIGH at the CLK posedge, ENCLK must be HIGH.
    check_en_te_high_implies_enclk_high: assert property (
        @(posedge CLK) (EN && TE) |-> ENCLK
    );

    // EN LOW forces ENCLK LOW at the CLK posedge.
    check_en_low_forces_enclk_low: assert property (
        @(posedge CLK) (!EN) |-> (!ENCLK)
    );

    // TE LOW forces ENCLK LOW at the CLK posedge.
    check_te_low_forces_enclk_low: assert property (
        @(posedge CLK) (!TE) |-> (!ENCLK)
    );

    // A rising ENCLK between posedges implies EN or TE rose.
    check_enclk_rise_caused_by_input_rise: assert property (
        @(posedge CLK) $rose(ENCLK) |-> ($rose(EN) || $rose(TE))
    );

    // A falling ENCLK between posedges implies EN or TE fell.
    check_enclk_fall_caused_by_input_fall: assert property (
        @(posedge CLK) $fell(ENCLK) |-> ($fell(EN) || $fell(TE))
    );

    // If EN rises and TE is HIGH at the posedge, ENCLK must rise.
    check_en_rise_with_te_high_makes_enclk_rise: assert property (
        @(posedge CLK) ($rose(EN) && (TE == 1'b1)) |-> $rose(ENCLK)
    );

    // If TE rises and EN is HIGH at the posedge, ENCLK must rise.
    check_te_rise_with_en_high_makes_enclk_rise: assert property (
        @(posedge CLK) ($rose(TE) && (EN == 1'b1)) |-> $rose(ENCLK)
    );

    // If EN falls while TE is HIGH across posedges, ENCLK must fall.
    check_en_fall_with_te_high_makes_enclk_fall: assert property (
        @(posedge CLK) ($fell(EN) && (TE == 1'b1) && ($past(TE) == 1'b1)) |-> $fell(ENCLK)
    );

    // If TE falls while EN is HIGH across posedges, ENCLK must fall.
    check_te_fall_with_en_high_makes_enclk_fall: assert property (
        @(posedge CLK) ($fell(TE) && (EN == 1'b1) && ($past(EN) == 1'b1)) |-> $fell(ENCLK)
    );
endmodule