module rising_edge_detector_sva (
    input logic IN,
    input logic CLK,
    input logic OUT
);

    // Sequential logic sampled on CLK; the RTL has no reset.
    // A sampled rising edge on IN produces a pulse on OUT in the next cycle.
    check_in_rise_generates_pulse: assert property (
        @(posedge CLK) (!$initstate && IN && !$past(IN)) |=> OUT
    );

    // A sampled low IN forces OUT low in the next cycle.
    check_low_in_no_pulse: assert property (
        @(posedge CLK) (!IN) |=> !OUT
    );

    // A sustained high IN does not retrigger OUT.
    check_steady_high_no_pulse: assert property (
        @(posedge CLK) (!$initstate && IN && $past(IN)) |=> !OUT
    );

    // A high OUT must have come from a previously sampled high IN.
    check_out_requires_prior_high_in: assert property (
        @(posedge CLK) (!$initstate && OUT) |-> $past(IN)
    );

    // OUT cannot remain high for two consecutive sampled cycles.
    check_out_single_cycle_pulse: assert property (
        @(posedge CLK) (!$initstate && OUT) |=> !OUT
    );

endmodule