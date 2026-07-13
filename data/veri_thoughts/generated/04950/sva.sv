module myClockGate_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // With no test override and EN low, the gated clock output is low.
    check_gate_disabled_low: assert property (
        @(posedge CLK) (!TE && !EN) |-> !ENCLK
    );

    // A low functional-mode output stays low while TE remains low and EN stays high.
    check_functional_low_is_sticky: assert property (
        @(posedge CLK) (!TE && EN && !ENCLK) ##1 (!TE && EN) |-> !ENCLK
    );

    // A high functional-mode output stays high while TE remains low and EN stays high.
    check_functional_high_is_sticky: assert property (
        @(posedge CLK) (!TE && EN && ENCLK) ##1 (!TE && EN) |-> ENCLK
    );

    // A test-enabled capture with EN high makes the next functional-mode output high.
    check_test_capture_sets_functional_high: assert property (
        @(posedge CLK) (TE && EN) ##1 (!TE && EN) |-> ENCLK
    );

    // A captured high value survives an intervening cycle with EN low.
    check_captured_high_survives_disable: assert property (
        @(posedge CLK) (TE && EN) ##1 (!EN) ##1 (!TE && EN) |-> ENCLK
    );

endmodule