module logic_circuit_sva (
    input logic Q,
    input logic CLK,
    input logic D,
    input logic SCD,
    input logic SCE,
    input logic Q_out
);

    // Clock: CLK
    // Reset: none
    // Mixed logic: combinational select feeding sequential Q_out

    // When SCE is low, Q_out captures D on the next clock.
    check_capture_d_when_sce_low: assert property (
        @(posedge CLK)
        (SCE === 1'b0) |=> (Q_out === $past(D))
    );

    // When SCE is high, Q_out captures SCD on the next clock.
    check_capture_scd_when_sce_high: assert property (
        @(posedge CLK)
        (SCE === 1'b1) |=> (Q_out === $past(SCD))
    );

    // When SCE is neither 0 nor 1, Q_out holds its previous value.
    check_hold_when_sce_unknown: assert property (
        @(posedge CLK)
        ((SCE !== 1'b0) && (SCE !== 1'b1)) |=> (Q_out === $past(Q_out))
    );

endmodule