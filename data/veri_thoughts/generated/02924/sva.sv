module mux4to1_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] C,
    input logic [3:0] D,
    input logic S0,
    input logic S1,
    input logic Y
);
    ///// 4:1 mux selection rules (sampled on S0/S1 edges) /////
    // When S1S0==00, Y equals A[0].
    check_sel_00_routes_A0: assert property (
        @(posedge S0 or posedge S1) ((S1 == 1'b0) && (S0 == 1'b0)) |-> (Y == A[0])
    );

    // When S1S0==01, Y equals B[0].
    check_sel_01_routes_B0: assert property (
        @(posedge S0 or posedge S1) ((S1 == 1'b0) && (S0 == 1'b1)) |-> (Y == B[0])
    );

    // When S1S0==10, Y equals C[0].
    check_sel_10_routes_C0: assert property (
        @(posedge S0 or posedge S1) ((S1 == 1'b1) && (S0 == 1'b0)) |-> (Y == C[0])
    );

    // When S1S0==11, Y equals D[0].
    check_sel_11_routes_D0: assert property (
        @(posedge S0 or posedge S1) ((S1 == 1'b1) && (S0 == 1'b1)) |-> (Y == D[0])
    );

    // Y equals the mux function of S1/S0 selecting the LSB of A/B/C/D.
    check_mux_function_equivalence: assert property (
        @(posedge S0 or posedge S1)
            (Y == (S1 ? (S0 ? D[0] : C[0]) : (S0 ? B[0] : A[0])))
    );

    // On any change to 00, Y updates to A[0] in the same cycle.
    check_update_on_to_00: assert property (
        @(posedge S0 or posedge S1)
            ($past({S1,S0}) != 2'b00 && {S1,S0} == 2'b00) |-> (Y == A[0])
    );

    // On any change to 01, Y updates to B[0] in the same cycle.
    check_update_on_to_01: assert property (
        @(posedge S0 or posedge S1)
            ($past({S1,S0}) != 2'b01 && {S1,S0} == 2'b01) |-> (Y == B[0])
    );

    // On any change to 10, Y updates to C[0] in the same cycle.
    check_update_on_to_10: assert property (
        @(posedge S0 or posedge S1)
            ($past({S1,S0}) != 2'b10 && {S1,S0} == 2'b10) |-> (Y == C[0])
    );

    // On any change to 11, Y updates to D[0] in the same cycle.
    check_update_on_to_11: assert property (
        @(posedge S0 or posedge S1)
            ($past({S1,S0}) != 2'b11 && {S1,S0} == 2'b11) |-> (Y == D[0])
    );
endmodule