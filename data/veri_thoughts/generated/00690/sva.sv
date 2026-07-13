module my_module_sva (
    input logic X,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    ///// Functional correctness /////
    // X equals the defined boolean function of inputs.
    check_functional_equivalence: assert property (
        @(posedge VPWR) X == (A1 & A2 & A3 & ~B1 & ~B2 & VPWR & ~VGND & VPB & ~VNB)
    );

    ///// Gating: any required-true input low forces X low /////
    // A1 low forces X low.
    gate_A1_low_forces_X0: assert property (
        @(posedge VPWR) (!A1) |-> (X == 1'b0)
    );
    // A2 low forces X low.
    gate_A2_low_forces_X0: assert property (
        @(posedge VPWR) (!A2) |-> (X == 1'b0)
    );
    // A3 low forces X low.
    gate_A3_low_forces_X0: assert property (
        @(posedge VPWR) (!A3) |-> (X == 1'b0)
    );

    ///// Gating: any required-false input high forces X low /////
    // B1 high forces X low.
    gate_B1_high_forces_X0: assert property (
        @(posedge VPWR) (B1) |-> (X == 1'b0)
    );
    // B2 high forces X low.
    gate_B2_high_forces_X0: assert property (
        @(posedge VPWR) (B2) |-> (X == 1'b0)
    );

    ///// Power/body rails gating /////
    // VPWR low forces X low.
    gate_VPWR_low_forces_X0: assert property (
        @(posedge VPWR) (!VPWR) |-> (X == 1'b0)
    );
    // VGND high forces X low.
    gate_VGND_high_forces_X0: assert property (
        @(posedge VPWR) (VGND) |-> (X == 1'b0)
    );
    // VPB low forces X low.
    gate_VPB_low_forces_X0: assert property (
        @(posedge VPWR) (!VPB) |-> (X == 1'b0)
    );
    // VNB high forces X low.
    gate_VNB_high_forces_X0: assert property (
        @(posedge VPWR) (VNB) |-> (X == 1'b0)
    );

    ///// Transition sanity /////
    // X can only rise when all required conditions are met.
    check_X_rise_requires_minterm: assert property (
        @(posedge VPWR) $rose(X) |-> (A1 & A2 & A3 & ~B1 & ~B2 & VPWR & ~VGND & VPB & ~VNB)
    );
    // X can only fall when the minterm is not satisfied.
    check_X_fall_requires_not_minterm: assert property (
        @(posedge VPWR) $fell(X) |-> !(A1 & A2 & A3 & ~B1 & ~B2 & VPWR & ~VGND & VPB & ~VNB)
    );

endmodule