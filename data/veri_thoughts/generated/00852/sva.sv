module my_or_gate_sva (
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    ///// Functional equivalence to RTL assign /////
    // X matches A|B|C|D_N when A rises.
    check_or_equiv_on_A_posedge: assert property (
        @(posedge A) X == (A | B | C | D_N)
    );
    // X matches A|B|C|D_N when A falls.
    check_or_equiv_on_A_negedge: assert property (
        @(negedge A) X == (A | B | C | D_N)
    );
    // X matches A|B|C|D_N when B rises.
    check_or_equiv_on_B_posedge: assert property (
        @(posedge B) X == (A | B | C | D_N)
    );
    // X matches A|B|C|D_N when B falls.
    check_or_equiv_on_B_negedge: assert property (
        @(negedge B) X == (A | B | C | D_N)
    );
    // X matches A|B|C|D_N when C rises.
    check_or_equiv_on_C_posedge: assert property (
        @(posedge C) X == (A | B | C | D_N)
    );
    // X matches A|B|C|D_N when C falls.
    check_or_equiv_on_C_negedge: assert property (
        @(negedge C) X == (A | B | C | D_N)
    );
    // X matches A|B|C|D_N when D_N rises.
    check_or_equiv_on_DN_posedge: assert property (
        @(posedge D_N) X == (A | B | C | D_N)
    );
    // X matches A|B|C|D_N when D_N falls.
    check_or_equiv_on_DN_negedge: assert property (
        @(negedge D_N) X == (A | B | C | D_N)
    );

    ///// Independence from unused power/body pins /////
    // VPWR changes do not affect X if A,B,C,D_N are stable.
    check_x_independent_of_vpwr_posedge: assert property (
        @(posedge VPWR) ((A == $past(A)) && (B == $past(B)) && (C == $past(C)) && (D_N == $past(D_N))) |-> (X == $past(X))
    );
    // VPWR changes do not affect X if A,B,C,D_N are stable.
    check_x_independent_of_vpwr_negedge: assert property (
        @(negedge VPWR) ((A == $past(A)) && (B == $past(B)) && (C == $past(C)) && (D_N == $past(D_N))) |-> (X == $past(X))
    );
    // VGND changes do not affect X if A,B,C,D_N are stable.
    check_x_independent_of_vgnd_posedge: assert property (
        @(posedge VGND) ((A == $past(A)) && (B == $past(B)) && (C == $past(C)) && (D_N == $past(D_N))) |-> (X == $past(X))
    );
    // VGND changes do not affect X if A,B,C,D_N are stable.
    check_x_independent_of_vgnd_negedge: assert property (
        @(negedge VGND) ((A == $past(A)) && (B == $past(B)) && (C == $past(C)) && (D_N == $past(D_N))) |-> (X == $past(X))
    );
endmodule