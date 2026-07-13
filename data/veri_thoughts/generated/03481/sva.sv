module sky130_fd_sc_hdll__a222oi_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic C1,
    input logic C2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y matches the implemented NAND/AND/BUF function.
    check_function_equation: assert property (
        @($global_clock)
        Y == (~(A2 & A1) & ~(B2 & B1) & ~(C2 & C1))
    );

    // A1 and A2 both high force Y low.
    check_a_pair_forces_low: assert property (
        @($global_clock)
        ((A1 & A2) == 1'b1) |-> (Y == 1'b0)
    );

    // B1 and B2 both high force Y low.
    check_b_pair_forces_low: assert property (
        @($global_clock)
        ((B1 & B2) == 1'b1) |-> (Y == 1'b0)
    );

    // C1 and C2 both high force Y low.
    check_c_pair_forces_low: assert property (
        @($global_clock)
        ((C1 & C2) == 1'b1) |-> (Y == 1'b0)
    );

    // Y is high when no input pair is simultaneously high.
    check_no_active_pair_drives_high: assert property (
        @($global_clock)
        (((A1 & A2) == 1'b0) && ((B1 & B2) == 1'b0) && ((C1 & C2) == 1'b0)) |-> (Y == 1'b1)
    );

    // A high Y means every input pair avoids a simultaneous high.
    check_high_implies_no_active_pair: assert property (
        @($global_clock)
        (Y == 1'b1) |-> (((A1 & A2) == 1'b0) && ((B1 & B2) == 1'b0) && ((C1 & C2) == 1'b0))
    );

    // A low Y means at least one input pair is simultaneously high.
    check_low_implies_some_active_pair: assert property (
        @($global_clock)
        (Y == 1'b0) |-> (((A1 & A2) == 1'b1) || ((B1 & B2) == 1'b1) || ((C1 & C2) == 1'b1))
    );

    // All six data inputs low produce a high output.
    check_all_zero_inputs_drive_high: assert property (
        @($global_clock)
        ((A1 == 1'b0) && (A2 == 1'b0) && (B1 == 1'b0) && (B2 == 1'b0) && (C1 == 1'b0) && (C2 == 1'b0)) |-> (Y == 1'b1)
    );

    // All six data inputs high produce a low output.
    check_all_one_inputs_drive_low: assert property (
        @($global_clock)
        ((A1 == 1'b1) && (A2 == 1'b1) && (B1 == 1'b1) && (B2 == 1'b1) && (C1 == 1'b1) && (C2 == 1'b1)) |-> (Y == 1'b0)
    );

endmodule