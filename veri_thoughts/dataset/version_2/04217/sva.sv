module my_module_sva (
    input logic D,
    input logic Q,
    input logic DE,
    input logic SCD,
    input logic SCE,
    input logic CLK
);

    // In scan-hold mode, Q must retain its previous value.
    check_scan_hold: assert property (
        @(posedge CLK)
        ((SCD == 1'b0) && (SCE == 1'b1)) |=> (Q == $past(Q))
    );

    // Outside scan-hold, DE high causes Q to capture D on the next cycle.
    check_capture_when_enabled: assert property (
        @(posedge CLK)
        (!((SCD == 1'b0) && (SCE == 1'b1)) && (DE == 1'b1)) |=> (Q == $past(D))
    );

    // Outside scan-hold, DE low leaves Q unchanged.
    check_hold_when_disabled: assert property (
        @(posedge CLK)
        (!((SCD == 1'b0) && (SCE == 1'b1)) && (DE == 1'b0)) |=> (Q == $past(Q))
    );

    // A change on Q must come from an enabled non-scan capture in the prior cycle.
    check_change_requires_capture: assert property (
        @(posedge CLK)
        (Q != $past(Q)) |-> ($past(!((SCD == 1'b0) && (SCE == 1'b1)) && (DE == 1'b1)) && (Q == $past(D)))
    );

endmodule