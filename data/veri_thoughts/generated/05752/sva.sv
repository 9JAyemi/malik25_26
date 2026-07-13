module sky130_fd_sc_hs__sdfxbp_2_sva (
    input logic CLK,
    input logic D,
    input logic Q,
    input logic Q_N,
    input logic SCD,
    input logic SCE
);

    // Q_N is always the sampled inverse of Q.
    check_qn_inverse_of_q: assert property (
        @(posedge CLK) (Q_N === ~Q)
    );

    // When scan is enabled, Q captures SCD on the next sampled cycle.
    check_scan_loads_q_from_scd: assert property (
        @(posedge CLK) (SCE === 1'b1) |=> (Q === $past(SCD))
    );

    // When scan is not enabled, Q captures D on the next sampled cycle.
    check_data_loads_q_from_d: assert property (
        @(posedge CLK) (SCE !== 1'b1) |=> (Q === $past(D))
    );

    // When scan is enabled, Q_N reflects the inverse of prior SCD.
    check_scan_loads_qn_from_scd: assert property (
        @(posedge CLK) (SCE === 1'b1) |=> (Q_N === (~$past(SCD)))
    );

    // When scan is not enabled, Q_N reflects the inverse of prior D.
    check_data_loads_qn_from_d: assert property (
        @(posedge CLK) (SCE !== 1'b1) |=> (Q_N === (~$past(D)))
    );

endmodule