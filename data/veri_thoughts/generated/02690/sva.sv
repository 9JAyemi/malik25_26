module mux4_ctrl_sva (
    input  logic        CLK,   // external verification clock (RTL has no clock/reset)
    input  logic [7:0]  A,
    input  logic [7:0]  B,
    input  logic [7:0]  C,
    input  logic [7:0]  D,
    input  logic        ctrl,
    input  logic [7:0]  out
);
    // RTL is purely combinational: ctrl=0 selects A, ctrl=1 selects D, otherwise out=0.

    // When ctrl==0, out equals A.
    check_ctrl0_selects_A: assert property (
        @(posedge CLK) (ctrl == 1'b0) |-> (out == A)
    );

    // When ctrl==1, out equals D.
    check_ctrl1_selects_D: assert property (
        @(posedge CLK) (ctrl == 1'b1) |-> (out == D)
    );

    // If ctrl is X/Z, out must be 0.
    check_default_zero_on_unknown_ctrl: assert property (
        @(posedge CLK) (ctrl !== 1'b0 && ctrl !== 1'b1) |-> (out == 8'h00)
    );

    // With ctrl held 0 and A stable, out stays stable.
    check_stable_out_when_ctrl0_A_stable: assert property (
        @(posedge CLK) (ctrl == 1'b0) && $stable(ctrl) && $stable(A) |-> $stable(out)
    );

    // With ctrl held 1 and D stable, out stays stable.
    check_stable_out_when_ctrl1_D_stable: assert property (
        @(posedge CLK) (ctrl == 1'b1) && $stable(ctrl) && $stable(D) |-> $stable(out)
    );

    // With ctrl held 0, a change on A causes a change on out.
    check_A_change_propagates_when_ctrl0: assert property (
        @(posedge CLK) (ctrl == 1'b0) && $stable(ctrl) && $changed(A) |-> $changed(out)
    );

    // With ctrl held 1, a change on D causes a change on out.
    check_D_change_propagates_when_ctrl1: assert property (
        @(posedge CLK) (ctrl == 1'b1) && $stable(ctrl) && $changed(D) |-> $changed(out)
    );

    // On ctrl rising edge, out reflects D.
    check_out_on_ctrl_rise: assert property (
        @(posedge CLK) $rose(ctrl) |-> (out == D)
    );

    // On ctrl falling edge, out reflects A.
    check_out_on_ctrl_fall: assert property (
        @(posedge CLK) $fell(ctrl) |-> (out == A)
    );
endmodule