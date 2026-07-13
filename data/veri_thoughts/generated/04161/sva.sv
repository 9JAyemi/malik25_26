module clock_gate_high_register_add_w31_0_2_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK,
    input logic ECK
);

    // ENCLK is a direct copy of the internal latch output on CLK samples.
    check_enclk_matches_eck_on_clk: assert property (
        @(posedge CLK) ENCLK == ECK
    );

    // ENCLK is a direct copy of the internal latch output on TE samples.
    check_enclk_matches_eck_on_te: assert property (
        @(posedge TE) ENCLK == ECK
    );

    // TE high at a CLK edge forces the stored enable high by the next CLK sample.
    check_te_high_on_clk_sets_high: assert property (
        @(posedge CLK) TE |=> (ECK && ENCLK)
    );

    // EN high with TE low at a CLK edge loads a high value by the next CLK sample.
    check_en_high_without_te_sets_high: assert property (
        @(posedge CLK) (!TE && EN) |=> (ECK && ENCLK)
    );

    // A TE rising edge asynchronously sets the stored enable high by the next CLK sample.
    check_te_rise_sets_high_by_next_clk: assert property (
        @(posedge TE) 1'b1 |=> @(posedge CLK) (ECK && ENCLK)
    );

endmodule