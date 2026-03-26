module sky130_fd_sc_ls__o21ba_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // External sampling clock; DUT is purely combinational and has no reset.

    // X must match the exact RTL combinational equation.
    check_x_matches_equation: assert property (
        @(posedge clk)
        X === (A1 & A2 & ~B1_N & ~VPWR & ~VGND & ((VPB & ~VNB) | (~VPB & VNB)))
    );

    // All required true conditions must drive X high.
    check_full_enable_drives_x_high: assert property (
        @(posedge clk)
        (A1 === 1'b1 && A2 === 1'b1 && B1_N === 1'b0 && VPWR === 1'b0 && VGND === 1'b0 &&
         (((VPB === 1'b1) && (VNB === 1'b0)) || ((VPB === 1'b0) && (VNB === 1'b1))))
        |-> (X === 1'b1)
    );

    // A1 low forces X low.
    check_a1_low_forces_x_low: assert property (
        @(posedge clk)
        (A1 === 1'b0) |-> (X === 1'b0)
    );

    // A2 low forces X low.
    check_a2_low_forces_x_low: assert property (
        @(posedge clk)
        (A2 === 1'b0) |-> (X === 1'b0)
    );

    // B1_N high forces X low.
    check_b1n_high_forces_x_low: assert property (
        @(posedge clk)
        (B1_N === 1'b1) |-> (X === 1'b0)
    );

    // VPWR high forces X low.
    check_vpwr_high_forces_x_low: assert property (
        @(posedge clk)
        (VPWR === 1'b1) |-> (X === 1'b0)
    );

    // VGND high forces X low.
    check_vgnd_high_forces_x_low: assert property (
        @(posedge clk)
        (VGND === 1'b1) |-> (X === 1'b0)
    );

    // Equal body-bias pins force X low.
    check_equal_body_pins_force_x_low: assert property (
        @(posedge clk)
        (((VPB === 1'b0) && (VNB === 1'b0)) || ((VPB === 1'b1) && (VNB === 1'b1)))
        |-> (X === 1'b0)
    );

    // X high implies every enabling input condition is satisfied.
    check_x_high_implies_required_conditions: assert property (
        @(posedge clk)
        (X === 1'b1)
        |-> (A1 === 1'b1 && A2 === 1'b1 && B1_N === 1'b0 && VPWR === 1'b0 && VGND === 1'b0 &&
             (((VPB === 1'b1) && (VNB === 1'b0)) || ((VPB === 1'b0) && (VNB === 1'b1))))
    );

endmodule