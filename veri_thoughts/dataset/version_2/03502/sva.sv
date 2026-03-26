module flipflop_assertions (
    input logic D,
    input logic SCD,
    input logic SCE,
    input logic CLK,
    input logic Q,
    input logic Q_N
);

    // SCD clears the flop outputs on the next clock.
    check_scan_clear_outputs: assert property (
        @(posedge CLK) SCD |=> (Q == 1'b0) && (Q_N == 1'b1)
    );

    // SCD has priority over SCE when both are high.
    check_scan_clear_priority: assert property (
        @(posedge CLK) (SCD && SCE) |=> (Q == 1'b0) && (Q_N == 1'b1)
    );

    // With SCE high and SCD low, Q holds and Q_N follows the held Q complement.
    check_scan_enable_hold: assert property (
        @(posedge CLK) (!SCD && SCE) |=> (Q == $past(Q)) && (Q_N == ~($past(Q)))
    );

    // With both controls low, the flop loads D and drives its complement on Q_N.
    check_data_load: assert property (
        @(posedge CLK) (!SCD && !SCE) |=> (Q == $past(D)) && (Q_N == ~($past(D)))
    );

    // After each clocked update, Q_N is the complement of Q.
    check_outputs_complementary: assert property (
        @(posedge CLK) 1'b1 |=> (Q_N == ~Q)
    );

endmodule