module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // ENCLK is asserted on the next clock when both EN and TE are high.
    check_enclk_asserts_when_en_and_te_high: assert property (
        @(posedge CLK) (EN && TE) |=> (ENCLK == 1'b1)
    );

    // ENCLK is deasserted on the next clock when either EN or TE is low.
    check_enclk_deasserts_when_en_or_te_low: assert property (
        @(posedge CLK) (!EN || !TE) |=> (ENCLK == 1'b0)
    );

endmodule