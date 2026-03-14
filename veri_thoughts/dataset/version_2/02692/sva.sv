module my_and3_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    ///// Functional equivalence sampled on input/supply edges /////
    // On A rising edge, X equals ((A&B&C)==VPWR) && (VGND==0).
    check_eq_on_posedge_A: assert property (
        @(posedge A) X == (((A & B & C) == VPWR) && (VGND == 1'b0))
    );
    // On A falling edge, X equals ((A&B&C)==VPWR) && (VGND==0).
    check_eq_on_negedge_A: assert property (
        @(negedge A) X == (((A & B & C) == VPWR) && (VGND == 1'b0))
    );
    // On B rising edge, X equals ((A&B&C)==VPWR) && (VGND==0).
    check_eq_on_posedge_B: assert property (
        @(posedge B) X == (((A & B & C) == VPWR) && (VGND == 1'b0))
    );
    // On B falling edge, X equals ((A&B&C)==VPWR) && (VGND==0).
    check_eq_on_negedge_B: assert property (
        @(negedge B) X == (((A & B & C) == VPWR) && (VGND == 1'b0))
    );
    // On C rising edge, X equals ((A&B&C)==VPWR) && (VGND==0).
    check_eq_on_posedge_C: assert property (
        @(posedge C) X == (((A & B & C) == VPWR) && (VGND == 1'b0))
    );
    // On C falling edge, X equals ((A&B&C)==VPWR) && (VGND==0).
    check_eq_on_negedge_C: assert property (
        @(negedge C) X == (((A & B & C) == VPWR) && (VGND == 1'b0))
    );
    // On VPWR rising edge, X equals ((A&B&C)==VPWR) && (VGND==0).
    check_eq_on_posedge_VPWR: assert property (
        @(posedge VPWR) X == (((A & B & C) == VPWR) && (VGND == 1'b0))
    );
    // On VPWR falling edge, X equals ((A&B&C)==VPWR) && (VGND==0).
    check_eq_on_negedge_VPWR: assert property (
        @(negedge VPWR) X == (((A & B & C) == VPWR) && (VGND == 1'b0))
    );
    // On VGND rising edge, X equals ((A&B&C)==VPWR) && (VGND==0).
    check_eq_on_posedge_VGND: assert property (
        @(posedge VGND) X == (((A & B & C) == VPWR) && (VGND == 1'b0))
    );
    // On VGND falling edge, X equals ((A&B&C)==VPWR) && (VGND==0).
    check_eq_on_negedge_VGND: assert property (
        @(negedge VGND) X == (((A & B & C) == VPWR) && (VGND == 1'b0))
    );

    ///// Necessary conditions for X to be HIGH /////
    // If X rises, VGND must be 0.
    x_rise_requires_vgnd0: assert property (
        @(posedge X) VGND == 1'b0
    );
    // If X rises, (A&B&C) must equal VPWR.
    x_rise_requires_and_match_vpwr: assert property (
        @(posedge X) ((A & B & C) == VPWR)
    );

    ///// Supply-specific simplifications /////
    // With VPWR=1 and VGND=0, X equals A&B&C.
    x_when_vpwr1_vgnd0: assert property (
        @(posedge A) ((VPWR == 1'b1) && (VGND == 1'b0)) |-> (X == (A & B & C))
    );
    // With VPWR=0 and VGND=0, X equals ~(A&B&C).
    x_when_vpwr0_vgnd0: assert property (
        @(posedge A) ((VPWR == 1'b0) && (VGND == 1'b0)) |-> (X == ~(A & B & C))
    );
    // If VGND != 0, X must be 0.
    vgnd_nonzero_forces_x0: assert property (
        @(posedge VGND) (VGND != 1'b0) |-> (X == 1'b0)
    );
endmodule