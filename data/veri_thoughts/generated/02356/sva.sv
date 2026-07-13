module mux4to1_sva (
    input logic CLK,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic [1:0] S,
    input logic Y
);
    ///// Functional mapping /////
    // Y equals the 4:1 mux function of S selecting A/B/C/D.
    check_mux_equation: assert property (
        @(posedge CLK) Y == ((S == 2'b00) ? A :
                             (S == 2'b01) ? B :
                             (S == 2'b10) ? C : D)
    );

    // When S==00, Y must equal A.
    check_sel_00: assert property (
        @(posedge CLK) (S == 2'b00) |-> (Y == A)
    );

    // When S==01, Y must equal B.
    check_sel_01: assert property (
        @(posedge CLK) (S == 2'b01) |-> (Y == B)
    );

    // When S==10, Y must equal C.
    check_sel_10: assert property (
        @(posedge CLK) (S == 2'b10) |-> (Y == C)
    );

    // When S==11, Y must equal D.
    check_sel_11: assert property (
        @(posedge CLK) (S == 2'b11) |-> (Y == D)
    );

    ///// Independence from non-selected inputs /////
    // If S!=11 and only D changes, Y is unaffected (D not selected).
    independence_d_not_s11: assert property (
        @(posedge CLK) (S != 2'b11) && $stable(S) && $stable(A) && $stable(B) && $stable(C) && $changed(D) |-> $stable(Y)
    );

    // If S in {00,01} and only C changes, Y is unaffected (C not selected).
    independence_c_s00_or_s01: assert property (
        @(posedge CLK) (S inside {2'b00,2'b01}) && $stable(S) && $stable(A) && $stable(B) && $stable(D) && $changed(C) |-> $stable(Y)
    );

    // If S==00 and only B changes, Y is unaffected (B not selected).
    independence_b_s00: assert property (
        @(posedge CLK) (S == 2'b00) && $stable(S) && $stable(A) && $stable(C) && $stable(D) && $changed(B) |-> $stable(Y)
    );

    // If S!=00 and only A changes, Y is unaffected (A not selected).
    independence_a_not_s00: assert property (
        @(posedge CLK) (S != 2'b00) && $stable(S) && $stable(B) && $stable(C) && $stable(D) && $changed(A) |-> $stable(Y)
    );

    ///// Stability /////
    // If S and all data inputs are stable, Y must be stable.
    output_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable(S) && $stable(A) && $stable(B) && $stable(C) && $stable(D) |-> $stable(Y)
    );
endmodule