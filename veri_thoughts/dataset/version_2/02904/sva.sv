module sky130_fd_sc_hd__and4b_sva (
    input logic X,
    input logic A_N,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // Combinational equivalence: X == (~A_N & B & C & D).
    check_function_equivalence: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
            (X === ((~A_N) & B & C & D))
    );

    // A_N high forces X low.
    check_A_N_high_forces_X_low: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
            (A_N === 1'b1) |-> (X === 1'b0)
    );

    // B low forces X low.
    check_B_zero_forces_X_low: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
            (B === 1'b0) |-> (X === 1'b0)
    );

    // C low forces X low.
    check_C_zero_forces_X_low: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
            (C === 1'b0) |-> (X === 1'b0)
    );

    // D low forces X low.
    check_D_zero_forces_X_low: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
            (D === 1'b0) |-> (X === 1'b0)
    );

    // All inputs true (with A_N low) forces X high.
    check_all_inputs_true_forces_X_high: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
            ((A_N === 1'b0) && (B === 1'b1) && (C === 1'b1) && (D === 1'b1)) |-> (X === 1'b1)
    );

    // X high implies A_N low and B,C,D high.
    check_X_high_implies_inputs_true: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
            (X === 1'b1) |-> ((A_N === 1'b0) && (B === 1'b1) && (C === 1'b1) && (D === 1'b1))
    );

    // With inputs stable, X is stable.
    check_stable_inputs_imply_stable_X: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
            ($stable(A_N) && $stable(B) && $stable(C) && $stable(D)) |-> $stable(X)
    );

    // Falling B drives X low immediately.
    check_B_fall_forces_X_low: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
            $fell(B) |-> (X === 1'b0)
    );

    // Falling C drives X low immediately.
    check_C_fall_forces_X_low: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
            $fell(C) |-> (X === 1'b0)
    );

    // Falling D drives X low immediately.
    check_D_fall_forces_X_low: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
            $fell(D) |-> (X === 1'b0)
    );

    // Rising A_N drives X low immediately.
    check_A_N_rise_forces_X_low: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
            $rose(A_N) |-> (X === 1'b0)
    );

    // Falling A_N with others high drives X high immediately.
    check_A_N_fall_others_high_sets_X_high: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
            ($fell(A_N) && (B === 1'b1) && (C === 1'b1) && (D === 1'b1)) |-> (X === 1'b1)
    );

    // Rising B with A_N low and C,D high drives X high immediately.
    check_B_rise_others_true_sets_X_high: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
            ($rose(B) && (A_N === 1'b0) && (C === 1'b1) && (D === 1'b1)) |-> (X === 1'b1)
    );

    // Rising C with A_N low and B,D high drives X high immediately.
    check_C_rise_others_true_sets_X_high: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
            ($rose(C) && (A_N === 1'b0) && (B === 1'b1) && (D === 1'b1)) |-> (X === 1'b1)
    );

    // Rising D with A_N low and B,C high drives X high immediately.
    check_D_rise_others_true_sets_X_high: assert property (
        @(posedge A_N or negedge A_N or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D)
            ($rose(D) && (A_N === 1'b0) && (B === 1'b1) && (C === 1'b1)) |-> (X === 1'b1)
    );
endmodule