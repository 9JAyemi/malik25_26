module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // A low EN on the prior clock edge leaves ENCLK low at this sample.
    check_prev_en_low_forces_enclk_low: assert property (
        @(posedge CLK) disable iff ($initstate)
        ($past(EN) == 1'b0) |-> (ENCLK == 1'b0)
    );

    // A low EN on this clock edge forces ENCLK low by the next clock sample.
    check_en_low_forces_next_enclk_low: assert property (
        @(posedge CLK) disable iff ($initstate)
        (EN == 1'b0) |=> (ENCLK == 1'b0)
    );

    // A sampled low-to-high EN transition is not visible on ENCLK until after this edge.
    check_en_rise_seen_as_low_before_update: assert property (
        @(posedge CLK) disable iff ($initstate)
        $rose(EN) |-> (ENCLK == 1'b0)
    );

    // A high sampled ENCLK requires EN to have been high on the prior clock edge.
    check_enclk_high_requires_prev_en_high: assert property (
        @(posedge CLK) disable iff ($initstate)
        (ENCLK == 1'b1) |-> ($past(EN) == 1'b1)
    );

endmodule