module nand_gate_output_assertions(
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic Y,
    input integer count,
    input logic resetCounter
);

    // X on any checked input drives Y to X.
    check_y_unknown_on_y_rise: assert property (
        @(posedge Y)
        (
            (A_N  === 1'bx) || (B_N  === 1'bx) || (C    === 1'bx) || (D    === 1'bx) ||
            (VPWR === 1'bx) || (VGND === 1'bx) || (VPB  === 1'bx) || (VNB  === 1'bx)
        ) |-> (Y === 1'bx)
    );

    // The count window forces Y low when no checked input is X.
    check_y_low_window_on_y_rise: assert property (
        @(posedge Y)
        (
            !(
                (A_N  === 1'bx) || (B_N  === 1'bx) || (C    === 1'bx) || (D    === 1'bx) ||
                (VPWR === 1'bx) || (VGND === 1'bx) || (VPB  === 1'bx) || (VNB  === 1'bx)
            ) &&
            (count >= 32) && (count <= 39)
        ) |-> (Y === 1'b0)
    );

    // Otherwise Y matches the four-input NAND function.
    check_y_nand_on_y_rise: assert property (
        @(posedge Y)
        (
            !(
                (A_N  === 1'bx) || (B_N  === 1'bx) || (C    === 1'bx) || (D    === 1'bx) ||
                (VPWR === 1'bx) || (VGND === 1'bx) || (VPB  === 1'bx) || (VNB  === 1'bx)
            ) &&
            !((count >= 32) && (count <= 39))
        ) |-> (Y === ~(A_N & B_N & C & D))
    );

    // All-zero inputs assert resetCounter.
    check_resetcounter_high_on_y_rise: assert property (
        @(posedge Y)
        (
            (A_N  === 1'b0) && (B_N  === 1'b0) && (C    === 1'b0) && (D    === 1'b0) &&
            (VPWR === 1'b0) && (VGND === 1'b0) && (VPB  === 1'b0) && (VNB  === 1'b0)
        ) |-> (resetCounter === 1'b1)
    );

    // Any non-all-zero input combination deasserts resetCounter.
    check_resetcounter_low_on_y_rise: assert property (
        @(posedge Y)
        !(
            (A_N  === 1'b0) && (B_N  === 1'b0) && (C    === 1'b0) && (D    === 1'b0) &&
            (VPWR === 1'b0) && (VGND === 1'b0) && (VPB  === 1'b0) && (VNB  === 1'b0)
        ) |-> (resetCounter === 1'b0)
    );

    // X on any checked input drives Y to X.
    check_y_unknown_on_resetcounter_rise: assert property (
        @(posedge resetCounter)
        (
            (A_N  === 1'bx) || (B_N  === 1'bx) || (C    === 1'bx) || (D    === 1'bx) ||
            (VPWR === 1'bx) || (VGND === 1'bx) || (VPB  === 1'bx) || (VNB  === 1'bx)
        ) |-> (Y === 1'bx)
    );

    // The count window forces Y low when no checked input is X.
    check_y_low_window_on_resetcounter_rise: assert property (
        @(posedge resetCounter)
        (
            !(
                (A_N  === 1'bx) || (B_N  === 1'bx) || (C    === 1'bx) || (D    === 1'bx) ||
                (VPWR === 1'bx) || (VGND === 1'bx) || (VPB  === 1'bx) || (VNB  === 1'bx)
            ) &&
            (count >= 32) && (count <= 39)
        ) |-> (Y === 1'b0)
    );

    // Otherwise Y matches the four-input NAND function.
    check_y_nand_on_resetcounter_rise: assert property (
        @(posedge resetCounter)
        (
            !(
                (A_N  === 1'bx) || (B_N  === 1'bx) || (C    === 1'bx) || (D    === 1'bx) ||
                (VPWR === 1'bx) || (VGND === 1'bx) || (VPB  === 1'bx) || (VNB  === 1'bx)
            ) &&
            !((count >= 32) && (count <= 39))
        ) |-> (Y === ~(A_N & B_N & C & D))
    );

    // All-zero inputs assert resetCounter.
    check_resetcounter_high_on_resetcounter_rise: assert property (
        @(posedge resetCounter)
        (
            (A_N  === 1'b0) && (B_N  === 1'b0) && (C    === 1'b0) && (D    === 1'b0) &&
            (VPWR === 1'b0) && (VGND === 1'b0) && (VPB  === 1'b0) && (VNB  === 1'b0)
        ) |-> (resetCounter === 1'b1)
    );

    // Any non-all-zero input combination deasserts resetCounter.
    check_resetcounter_low_on_resetcounter_rise: assert property (
        @(posedge resetCounter)
        !(
            (A_N  === 1'b0) && (B_N  === 1'b0) && (C    === 1'b0) && (D    === 1'b0) &&
            (VPWR === 1'b0) && (VGND === 1'b0) && (VPB  === 1'b0) && (VNB  === 1'b0)
        ) |-> (resetCounter === 1'b0)
    );

    // Between Y rises, count either advances by one or has been reset to zero.
    check_count_progress_on_y_rise: assert property (
        @(posedge Y) disable iff (resetCounter)
        (count == 0) || (count == ($past(count) + 1))
    );

endmodule