module buf_4_xor_assertions (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);

    // X matches the implemented combinational function.
    check_output_equation: assert property (
        @(posedge clk)
        X == ((A ^ D) & VPWR & VGND & VPB & VNB)
    );

    // Any low power pin forces X low.
    check_any_supply_low_forces_zero: assert property (
        @(posedge clk)
        (!VPWR || !VGND || !VPB || !VNB) |-> !X
    );

    // With all supplies high and D low, X follows A.
    check_d_low_output_follows_a: assert property (
        @(posedge clk)
        (VPWR && VGND && VPB && VNB && !D) |-> (X == A)
    );

    // With all supplies high and D high, X is the inverse of A.
    check_d_high_output_inverts_a: assert property (
        @(posedge clk)
        (VPWR && VGND && VPB && VNB && D) |-> (X == ~A)
    );

    // With all supplies high, equal A and D drive X low.
    check_equal_inputs_drive_zero: assert property (
        @(posedge clk)
        (VPWR && VGND && VPB && VNB && (A == D)) |-> !X
    );

    // With all supplies high, different A and D drive X high.
    check_different_inputs_drive_one: assert property (
        @(posedge clk)
        (VPWR && VGND && VPB && VNB && (A != D)) |-> X
    );

    // Changing only B does not affect X.
    check_b_unused: assert property (
        @(posedge clk)
        ($changed(B) &&
         $stable(A) && $stable(C) && $stable(D) &&
         $stable(VPWR) && $stable(VGND) && $stable(VPB) && $stable(VNB)) |-> $stable(X)
    );

    // Changing only C does not affect X.
    check_c_unused: assert property (
        @(posedge clk)
        ($changed(C) &&
         $stable(A) && $stable(B) && $stable(D) &&
         $stable(VPWR) && $stable(VGND) && $stable(VPB) && $stable(VNB)) |-> $stable(X)
    );

    // With stable powered supplies and D, a change on A changes X.
    check_a_change_affects_x_when_powered: assert property (
        @(posedge clk)
        ($changed(A) && $stable(D) &&
         $stable(VPWR) && VPWR &&
         $stable(VGND) && VGND &&
         $stable(VPB) && VPB &&
         $stable(VNB) && VNB) |-> $changed(X)
    );

    // With stable powered supplies and A, a change on D changes X.
    check_d_change_affects_x_when_powered: assert property (
        @(posedge clk)
        ($changed(D) && $stable(A) &&
         $stable(VPWR) && VPWR &&
         $stable(VGND) && VGND &&
         $stable(VPB) && VPB &&
         $stable(VNB) && VNB) |-> $changed(X)
    );

endmodule