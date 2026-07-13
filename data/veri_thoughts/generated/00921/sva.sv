module my_module_sva (
    input  logic Q,
    input  logic CLK_N,
    input  logic D,
    input  logic SCD,
    input  logic SCE,
    input  logic RESET_B,
    input  logic VPWR,
    input  logic VGND,
    input  logic VPB,
    input  logic VNB
);
    // Clock: CLK_N (posedge). Reset: RESET_B active-low. Logic: combinational priority mux.

    // SCD high forces Q to 1.
    check_scd_forces_one: assert property (
        @(posedge CLK_N) disable iff (!RESET_B) SCD |-> (Q == 1'b1)
    );

    // SCD has priority over SCE when both are high.
    check_scd_over_sce: assert property (
        @(posedge CLK_N) disable iff (!RESET_B) (SCD && SCE) |-> (Q == 1'b1)
    );

    // With SCD low, SCE high forces Q to 0.
    check_sce_forces_zero_when_scd0: assert property (
        @(posedge CLK_N) disable iff (!RESET_B) (!SCD && SCE) |-> (Q == 1'b0)
    );

    // When SCD=0, SCE=0, and RESET_B=1, Q follows D.
    check_default_path_follows_D: assert property (
        @(posedge CLK_N) disable iff (!RESET_B) (!SCD && !SCE && (RESET_B == 1'b1)) |-> (Q == D)
    );

    // When SCD=0 and SCE=0 during reset, Q is 0.
    check_reset_clears_when_unselected: assert property (
        @(posedge CLK_N) (!RESET_B && !SCD && !SCE) |-> (Q == 1'b0)
    );

    // With SCD=0, SCE=1 during reset, Q remains 0 (SCE priority over reset default path).
    check_sce_priority_over_reset: assert property (
        @(posedge CLK_N) (!RESET_B && !SCD && SCE) |-> (Q == 1'b0)
    );

    // During reset, SCD still forces Q to 1.
    check_scd_overrides_reset: assert property (
        @(posedge CLK_N) (!RESET_B && SCD) |-> (Q == 1'b1)
    );

    // With SCD=1, SCE=1, and reset asserted, Q is 1 (SCD wins).
    check_all_high_scd_wins: assert property (
        @(posedge CLK_N) (!RESET_B && SCD && SCE) |-> (Q == 1'b1)
    );
endmodule