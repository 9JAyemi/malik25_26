module mux_dff_sva (
    input logic Q,
    input logic Q_N,
    input logic CLK,
    input logic D,
    input logic SCD,
    input logic SCE
);

// Q_N is always the bitwise complement of Q.
    check_qn_complement: assert property (
        @(posedge CLK) disable iff (1'b0) (Q_N == ~Q)
    );

// When SCE is low, the DFF is transparent and Q captures D on the next clock.
    check_sce_low_passthrough: assert property (
        @(posedge CLK) disable iff (1'b0) (!SCE) |=> (Q == $past(D))
    );

// When SCE is high, SCD selects D to Q on the next clock.
    check_sce_high_selects_d_when_scd_high: assert property (
        @(posedge CLK) disable iff (1'b0) SCE && SCD |=> (Q == $past(D))
    );

// When SCE is high and SCD is low, Q holds its previous value.
    check_sce_high_scd_low_holds_q: assert property (
        @(posedge CLK) disable iff (1'b0) SCE && !SCD |=> (Q == $past(Q))
    );

// When SCE is high and SCD is high, Q_N holds its previous value.
    check_sce_high_scd_high_holds_qn: assert property (
        @(posedge CLK) disable iff (1'b0) SCE && SCD |=> (Q_N == $past(Q_N))
    );

// When SCE is high and SCD is high, Q_N is the bitwise complement of Q.
    check_sce_high_scd_high_qn_complement: assert property (
        @(posedge CLK) disable iff (1'b0) SCE && SCD |-> (Q_N == ~Q)
    );

// When SCE is high and SCD is low, Q_N is the bitwise complement of Q.
    check_sce_high_scd_low_qn_complement: assert property (
        @(posedge CLK) disable iff (1'b0) SCE && !SCD |-> (Q_N == ~Q)
    );

endmodule
