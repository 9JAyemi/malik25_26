module cycloneive_dffe_sva (
    input logic D,
    input logic CLK,
    input logic ENA,
    input logic CLRN,
    input logic PRN,
    input logic Q
);

    // Active-low clear must force Q low when sampled low.
    check_clear_forces_q_low: assert property (
        @(posedge CLK) !CLRN |-> (Q == 1'b0)
    );

    // A sampled rise on Q must come from an enabled set or a captured 1.
    check_q_rise_requires_enabled_source: assert property (
        @(posedge CLK) disable iff (!CLRN || $initstate)
        $rose(Q) |-> ($past(CLRN) && $past(ENA) && ($past(PRN) || $past(D)))
    );

    // If Q rises without PRN set, the previous cycle must have captured D=1.
    check_q_rise_without_prn_requires_d_high: assert property (
        @(posedge CLK) disable iff (!CLRN || $initstate)
        ($rose(Q) && !$past(PRN)) |-> ($past(CLRN) && $past(ENA) && $past(D))
    );

    // If Q rises while previous D was 0, the rise must have come from PRN.
    check_q_rise_with_d_low_requires_prn_high: assert property (
        @(posedge CLK) disable iff (!CLRN || $initstate)
        ($rose(Q) && !$past(D)) |-> ($past(CLRN) && $past(ENA) && $past(PRN))
    );

    // Any sampled high Q must have a valid previous-cycle source.
    check_q_high_has_valid_previous_source: assert property (
        @(posedge CLK) disable iff (!CLRN || $initstate)
        Q |-> (
            $past(CLRN) &&
            (
                (!$past(ENA) && $past(Q)) ||
                ($past(ENA) && $past(PRN)) ||
                ($past(ENA) && !$past(PRN) && $past(D))
            )
        )
    );

endmodule