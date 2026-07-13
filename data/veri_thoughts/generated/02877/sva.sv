module sky130_fd_sc_hs__o21a_sva (
    input logic CLK,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic VGND
);
    // X equals AND of A1, A2, B1, VPWR, and VGND every cycle.
    check_functional_equivalence: assert property (
        @(posedge CLK) X == (A1 & A2 & B1 & VPWR & VGND)
    );

    // X high implies A1 is high.
    check_x_implies_a1: assert property (
        @(posedge CLK) X |-> A1
    );

    // X high implies A2 is high.
    check_x_implies_a2: assert property (
        @(posedge CLK) X |-> A2
    );

    // X high implies B1 is high.
    check_x_implies_b1: assert property (
        @(posedge CLK) X |-> B1
    );

    // X high implies VPWR is high.
    check_x_implies_vpwr: assert property (
        @(posedge CLK) X |-> VPWR
    );

    // X high implies VGND is high.
    check_x_implies_vgnd: assert property (
        @(posedge CLK) X |-> VGND
    );

    // All inputs high implies X is high.
    check_all_high_implies_x: assert property (
        @(posedge CLK) (A1 & A2 & B1 & VPWR & VGND) |-> X
    );

    // Any input low forces X low.
    check_any_low_forces_x_low: assert property (
        @(posedge CLK) (!A1 || !A2 || !B1 || !VPWR || !VGND) |-> (X == 1'b0)
    );

    // A rising edge on X requires all inputs high.
    check_x_rise_requires_all_high: assert property (
        @(posedge CLK) $rose(X) |-> (A1 & A2 & B1 & VPWR & VGND)
    );
endmodule