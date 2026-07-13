module clock_gate_d_ff_en_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);
    // ENCLK equals EN & CLK at the CLK rising edge.
    check_func_equivalence_on_clk: assert property (
        @(posedge CLK) ENCLK == (EN & CLK)
    );

    // A rising EN between samples causes a rising ENCLK between samples.
    check_en_rise_causes_enclk_rise: assert property (
        @(posedge CLK) $rose(EN) |-> $rose(ENCLK)
    );

    // A falling EN between samples causes a falling ENCLK between samples.
    check_en_fall_causes_enclk_fall: assert property (
        @(posedge CLK) $fell(EN) |-> $fell(ENCLK)
    );

    // ENCLK can only rise if EN is HIGH at the sample.
    check_enclk_rise_requires_en: assert property (
        @(posedge CLK) $rose(ENCLK) |-> (EN == 1'b1)
    );

    // EN=0 forces ENCLK=0 at the CLK rising edge.
    check_en_low_forces_enclk_low: assert property (
        @(posedge CLK) !EN |-> (ENCLK == 1'b0)
    );

    // Any change in sampled ENCLK must be due to a change in sampled EN.
    check_enclk_change_requires_en_change: assert property (
        @(posedge CLK) (ENCLK != $past(ENCLK)) |-> (EN != $past(EN))
    );

    // Any change in sampled EN causes a change in sampled ENCLK.
    check_en_change_causes_enclk_change: assert property (
        @(posedge CLK) $changed(EN) |-> $changed(ENCLK)
    );

    // On ENCLK rising edge, both EN and CLK must be HIGH.
    check_enclk_posedge_inputs_high: assert property (
        @(posedge ENCLK) (EN == 1'b1) && (CLK == 1'b1)
    );
endmodule