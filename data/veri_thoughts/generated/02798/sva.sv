module sky130_fd_sc_ls__o22a_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // Output equals the RTL expression.
    check_function_equivalence: assert property (
        @(posedge clk) disable iff (1'b0)
        X == ((A1 & A2) | (B1 & B2) | VPWR | VGND | VPB | VNB)
    );

    // If A1&A2 are HIGH, X must be HIGH.
    check_and_a_forces_x_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (A1 & A2) |-> X
    );

    // If B1&B2 are HIGH, X must be HIGH.
    check_and_b_forces_x_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (B1 & B2) |-> X
    );

    // If VPWR is HIGH, X must be HIGH.
    check_vpwr_forces_x_high: assert property (
        @(posedge clk) disable iff (1'b0)
        VPWR |-> X
    );

    // If VGND is HIGH, X must be HIGH.
    check_vgnd_forces_x_high: assert property (
        @(posedge clk) disable iff (1'b0)
        VGND |-> X
    );

    // If VPB is HIGH, X must be HIGH.
    check_vpb_forces_x_high: assert property (
        @(posedge clk) disable iff (1'b0)
        VPB |-> X
    );

    // If VNB is HIGH, X must be HIGH.
    check_vnb_forces_x_high: assert property (
        @(posedge clk) disable iff (1'b0)
        VNB |-> X
    );

    // If all inputs are LOW, X must be LOW.
    check_all_zero_forces_x_low: assert property (
        @(posedge clk) disable iff (1'b0)
        (!A1 && !A2 && !B1 && !B2 && !VPWR && !VGND && !VPB && !VNB) |-> (!X)
    );

    // X can only change if at least one input changed.
    check_x_change_requires_input_change: assert property (
        @(posedge clk) disable iff (1'b0)
        $changed(X) |-> ($changed(A1) || $changed(A2) || $changed(B1) || $changed(B2) ||
                         $changed(VPWR) || $changed(VGND) || $changed(VPB) || $changed(VNB))
    );

    // If all inputs are stable, X is stable.
    check_stable_inputs_imply_stable_x: assert property (
        @(posedge clk) disable iff (1'b0)
        $stable(A1) && $stable(A2) && $stable(B1) && $stable(B2) &&
        $stable(VPWR) && $stable(VGND) && $stable(VPB) && $stable(VNB) |-> $stable(X)
    );
endmodule