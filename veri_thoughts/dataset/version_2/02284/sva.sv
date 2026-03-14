module sky130_fd_sc_hd__or2b_sva (
    input logic A,
    input logic B_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB,
    input logic X
);

    // Output is never Z at any VPWR rising edge.
    check_output_never_z: assert property (
        @(posedge VPWR) X !== 1'bz
    );

    // When A and B_N are unchanged since last VPWR edge, X equals A | B_N.
    check_or_when_inputs_stable: assert property (
        @(posedge VPWR) (($past(A) === A) && ($past(B_N) === B_N)) |-> (X === (A | B_N))
    );

    // Stable 0/0 inputs across a VPWR cycle yield X=0.
    check_tt_00: assert property (
        @(posedge VPWR) (($past(A) === 1'b0) && (A === 1'b0) && ($past(B_N) === 1'b0) && (B_N === 1'b0)) |-> (X === 1'b0)
    );

    // Stable 0/1 inputs across a VPWR cycle yield X=1.
    check_tt_01: assert property (
        @(posedge VPWR) (($past(A) === 1'b0) && (A === 1'b0) && ($past(B_N) === 1'b1) && (B_N === 1'b1)) |-> (X === 1'b1)
    );

    // Stable 1/0 inputs across a VPWR cycle yield X=1.
    check_tt_10: assert property (
        @(posedge VPWR) (($past(A) === 1'b1) && (A === 1'b1) && ($past(B_N) === 1'b0) && (B_N === 1'b0)) |-> (X === 1'b1)
    );

    // Stable 1/1 inputs across a VPWR cycle yield X=1.
    check_tt_11: assert property (
        @(posedge VPWR) (($past(A) === 1'b1) && (A === 1'b1) && ($past(B_N) === 1'b1) && (B_N === 1'b1)) |-> (X === 1'b1)
    );

    // If inputs are unchanged for two VPWR cycles, X does not change across the last cycle.
    check_output_stable_after_two_cycles_of_input_stability: assert property (
        @(posedge VPWR) (($past(A,2) === A) && ($past(B_N,2) === B_N)) |-> (X === $past(X))
    );

    // With known inputs unchanged for two VPWR cycles, X is known (not X/Z).
    check_known_output_after_two_stable_cycles: assert property (
        @(posedge VPWR)
            ((A === 1'b0 || A === 1'b1) && (B_N === 1'b0 || B_N === 1'b1) &&
             ($past(A,2) === A) && ($past(B_N,2) === B_N))
            |-> ((X !== 1'bx) && (X !== 1'bz))
    );

    // Changes on VPB/VGND/VNB do not affect X when A and B_N are stable across a VPWR cycle.
    check_supplies_no_effect_when_inputs_stable: assert property (
        @(posedge VPWR)
            (($past(A) === A) && ($past(B_N) === B_N) &&
             (($past(VPB) !== VPB) || ($past(VGND) !== VGND) || ($past(VNB) !== VNB)))
            |-> (X === (A | B_N))
    );

    // With inputs stable for two cycles, X remains unchanged even if supplies toggle between cycles.
    check_supplies_no_effect_after_two_stable_cycles: assert property (
        @(posedge VPWR)
            (($past(A,2) === A) && ($past(B_N,2) === B_N) &&
             (($past(VPB) !== VPB) || ($past(VGND) !== VGND) || ($past(VNB) !== VNB)))
            |-> (X === $past(X))
    );

endmodule