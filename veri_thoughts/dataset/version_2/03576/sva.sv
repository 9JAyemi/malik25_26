module register_adder_clock_gate_assertions (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // A high pulse appears on the next high phase when EN is high and TE is low.
    check_pulse_when_enabled: assert property (
        @(posedge CLK) (EN && !TE) |=> @(negedge CLK) (ENCLK == 1'b1)
    );

    // No high pulse appears on the next high phase when the gate condition is false.
    check_no_pulse_when_blocked: assert property (
        @(posedge CLK) (!(EN && !TE)) |=> @(negedge CLK) (ENCLK == 1'b0)
    );

    // TE overrides EN and suppresses the gated clock pulse.
    check_test_enable_overrides_enable: assert property (
        @(posedge CLK) (EN && TE) |=> @(negedge CLK) (ENCLK == 1'b0)
    );

    // ENCLK is low at every sampled rising edge.
    check_enclk_low_on_rising_edge: assert property (
        @(posedge CLK) (ENCLK == 1'b0)
    );

endmodule