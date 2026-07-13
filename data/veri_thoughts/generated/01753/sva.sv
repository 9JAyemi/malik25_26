module my_or4bb_sva (
    input logic A,
    input logic B,
    input logic C_N,
    input logic D_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);
    // No explicit clock/reset in RTL; combinational logic; sample on posedge $global_clock.

    // Local derived conditions for readability
    logic drive_en;        // OR gate enable to the bufif1 control
    logic disable_cond;    // Condition when bufif1 is disabled
    logic pwrgood_val;     // Power-good expression

    assign drive_en    = (A | B | (~(C_N & D_N)));
    assign disable_cond = (~drive_en); // Equivalent to (!A && !B && C_N && D_N)
    assign pwrgood_val = ((VPWR > VPB) && (VNB > VGND));

    // When disabled (A=0,B=0,C_N=1,D_N=1), X must be high-Z.
    tri_when_disabled: assert property (
        @(posedge $global_clock) disable_cond |-> (X === 1'bz)
    );

    // When enabled by any input (A=1 or B=1 or C_N=0 or D_N=0), X must not be high-Z.
    driven_when_enabled: assert property (
        @(posedge $global_clock) drive_en |-> (X !== 1'bz)
    );

    // X is high-Z only when the disable condition holds.
    z_implies_disabled: assert property (
        @(posedge $global_clock) (X === 1'bz) |-> disable_cond
    );

    // When enabled, X must equal the pwrgood expression.
    x_matches_pwrgood_when_enabled: assert property (
        @(posedge $global_clock) drive_en |-> (X === pwrgood_val)
    );

    // When enabled and pwrgood is definitively 1, X must be 1.
    x_is_one_when_pwrgood_true: assert property (
        @(posedge $global_clock) (drive_en && (pwrgood_val === 1'b1)) |-> (X === 1'b1)
    );

    // When enabled and pwrgood is definitively 0, X must be 0.
    x_is_zero_when_pwrgood_false: assert property (
        @(posedge $global_clock) (drive_en && (pwrgood_val === 1'b0)) |-> (X === 1'b0)
    );

    // If A alone enables the path, X must equal pwrgood.
    a_enables_output: assert property (
        @(posedge $global_clock) (A === 1'b1) |-> (X === pwrgood_val)
    );

    // If B alone enables the path, X must equal pwrgood.
    b_enables_output: assert property (
        @(posedge $global_clock) (B === 1'b1) |-> (X === pwrgood_val)
    );

    // If C_N is low, NAND output is 1 -> OR enables -> X equals pwrgood.
    cn_low_enables_output: assert property (
        @(posedge $global_clock) (C_N === 1'b0) |-> (X === pwrgood_val)
    );

    // If D_N is low, NAND output is 1 -> OR enables -> X equals pwrgood.
    dn_low_enables_output: assert property (
        @(posedge $global_clock) (D_N === 1'b0) |-> (X === pwrgood_val)
    );

endmodule