module or4_2_custom_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X must equal the OR of A, B, C, and D.
    check_or_function: assert property (
        @($global_clock) X == (A | B | C | D)
    );

    // X must be low when all inputs are low.
    check_all_inputs_low: assert property (
        @($global_clock) (!A && !B && !C && !D) |-> !X
    );

    // X must be high when any input is high.
    check_any_input_high: assert property (
        @($global_clock) (A || B || C || D) |-> X
    );

    // X must be low when the OR stage is low.
    check_or_stage_low: assert property (
        @($global_clock) !((A | B | C | D)) |-> !X
    );

    // X must be high when the OR stage is high.
    check_or_stage_high: assert property (
        @($global_clock) ((A | B | C | D)) |-> X
    );

    // X must not depend on VPWR.
    check_vpwr_independent: assert property (
        @($global_clock) $stable({A, B, C, D}) && $changed(VPWR) |-> $stable(X)
    );

    // X must not depend on VGND.
    check_vgnd_independent: assert property (
        @($global_clock) $stable({A, B, C, D}) && $changed(VGND) |-> $stable(X)
    );

    // X must not depend on VPB.
    check_vpb_independent: assert property (
        @($global_clock) $stable({A, B, C, D}) && $changed(VPB) |-> $stable(X)
    );

    // X must not depend on VNB.
    check_vnb_independent: assert property (
        @($global_clock) $stable({A, B, C, D}) && $changed(VNB) |-> $stable(X)
    );

endmodule