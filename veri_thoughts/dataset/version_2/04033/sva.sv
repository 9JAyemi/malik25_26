module or_gate_power_good_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // X must match the implemented OR-and-power-good equation.
    check_output_function: assert property (
        @($global_clock) X === ((A | B | C) & VPWR & VGND)
    );

    // X must be low when all data inputs are low.
    check_output_low_when_inputs_low: assert property (
        @($global_clock) ((A | B | C) === 1'b0) |-> (X === 1'b0)
    );

    // X must be low when VPWR is low.
    check_output_low_when_vpwr_low: assert property (
        @($global_clock) (VPWR === 1'b0) |-> (X === 1'b0)
    );

    // X must be low when VGND is low.
    check_output_low_when_vgnd_low: assert property (
        @($global_clock) (VGND === 1'b0) |-> (X === 1'b0)
    );

    // X must be high when any data input is high and both power terms are high.
    check_output_high_with_input_and_power: assert property (
        @($global_clock) (((A | B | C) === 1'b1) && (VPWR === 1'b1) && (VGND === 1'b1)) |-> (X === 1'b1)
    );

    // A high X implies at least one data input and both power terms are high.
    check_high_output_implies_drivers: assert property (
        @($global_clock) (X === 1'b1) |-> (((A | B | C) === 1'b1) && (VPWR === 1'b1) && (VGND === 1'b1))
    );

    // Changing VPB alone must not affect X.
    check_vpb_independent_of_output: assert property (
        @($global_clock)
        (!$initstate && $changed(VPB) && $stable(A) && $stable(B) && $stable(C) && $stable(VPWR) && $stable(VGND) && $stable(VNB))
        |-> $stable(X)
    );

    // Changing VNB alone must not affect X.
    check_vnb_independent_of_output: assert property (
        @($global_clock)
        (!$initstate && $changed(VNB) && $stable(A) && $stable(B) && $stable(C) && $stable(VPWR) && $stable(VGND) && $stable(VPB))
        |-> $stable(X)
    );

endmodule