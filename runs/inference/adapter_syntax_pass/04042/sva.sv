module clock_gate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // ENCLK is high on the first clock after a sampled enable cycle.
    check_enclk_sets_high_after_enable: assert property (
        @(posedge CLK) disable iff ($initstate)
        ($past(TE) && $past(EN)) |-> (ENCLK == 1'b1)
    );

    // ENCLK is low on the first clock after a sampled disable cycle.
    check_enclk_sets_low_after_disable: assert property (
        @(posedge CLK) disable iff ($initstate)
        ($past(TE) && !$past(EN)) |-> (ENCLK == 1'b0)
    );

    // ENCLK holds its value when the enable control is not sampled high.
    check_enclk_holds_when_enable_not_sampled: assert property (
        @(posedge CLK) disable iff ($initstate)
        (!$past(TE)) |-> (ENCLK == $past(ENCLK))
    );

endmodule