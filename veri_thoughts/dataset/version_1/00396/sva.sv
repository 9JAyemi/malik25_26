module SNPS_CLOCK_GATE_HIGH_d_ff_en_W64_0_4_sva (
    input logic CLK,
    input logic EN,
    input logic TE,
    input logic ENCLK
);

    // When enabled with TE high, the next sampled output must be high.
    check_capture_high_when_enabled: assert property (
        @(posedge CLK) (EN && TE) |=> ENCLK
    );

    // When enabled with TE low, the next sampled output must be low.
    check_capture_low_when_enabled: assert property (
        @(posedge CLK) (EN && !TE) |=> !ENCLK
    );

    // When disabled, the next sampled output must be cleared low.
    check_clear_when_disabled: assert property (
        @(posedge CLK) (!EN) |=> !ENCLK
    );

    // A high output must come from EN and TE both being high on the prior clock.
    check_high_requires_prior_enable_and_te: assert property (
        @(posedge CLK) !$initstate && ENCLK |-> ($past(EN) && $past(TE))
    );

    // After the first clock, the output matches the prior cycle's registered function.
    check_registered_output_function: assert property (
        @(posedge CLK) !$initstate |-> (ENCLK == ($past(EN) ? $past(TE) : 1'b0))
    );

endmodule