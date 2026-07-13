module sky130_fd_sc_lp__or2_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // OR function holds on A rising edge.
    check_or_eq_on_posA: assert property (
        @(posedge A) X == (A | B)
    );

    // OR function holds on A falling edge.
    check_or_eq_on_negA: assert property (
        @(negedge A) X == (A | B)
    );

    // OR function holds on B rising edge.
    check_or_eq_on_posB: assert property (
        @(posedge B) X == (A | B)
    );

    // OR function holds on B falling edge.
    check_or_eq_on_negB: assert property (
        @(negedge B) X == (A | B)
    );

    // OR function holds on X rising edge.
    check_or_eq_on_posX: assert property (
        @(posedge X) X == (A | B)
    );

    // OR function holds on X falling edge.
    check_or_eq_on_negX: assert property (
        @(negedge X) X == (A | B)
    );

endmodule