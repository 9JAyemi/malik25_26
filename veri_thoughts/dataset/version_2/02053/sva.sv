module mux4to1_sva (
    input  logic CLK,
    input  logic A,
    input  logic B,
    input  logic C,
    input  logic D,
    input  logic S0,
    input  logic S1,
    input  logic Y
);
    // Select decoding terms are one-hot for any S1,S0 combination.
    check_select_terms_onehot: assert property (
        @(posedge CLK) $onehot({(~S1 & ~S0), (~S1 & S0), (S1 & ~S0), (S1 & S0)})
    );

    // Output matches the sum-of-products mux equation.
    check_mux_sop_function: assert property (
        @(posedge CLK) Y == ((A & ~S1 & ~S0) | (B & ~S1 & S0) | (C & S1 & ~S0) | (D & S1 & S0))
    );

    // When S1S0=00, Y equals A.
    check_select_00_match_A: assert property (
        @(posedge CLK) (~S1 && ~S0) |-> (Y == A)
    );

    // When S1S0=01, Y equals B.
    check_select_01_match_B: assert property (
        @(posedge CLK) (~S1 &&  S0) |-> (Y == B)
    );

    // When S1S0=10, Y equals C.
    check_select_10_match_C: assert property (
        @(posedge CLK) ( S1 && ~S0) |-> (Y == C)
    );

    // When S1S0=11, Y equals D.
    check_select_11_match_D: assert property (
        @(posedge CLK) ( S1 &&  S0) |-> (Y == D)
    );

    // When S1=0, Y is a 2:1 mux between A and B selected by S0.
    check_when_S1_low_2to1_AB: assert property (
        @(posedge CLK) (S1 == 1'b0) |-> (Y == (S0 ? B : A))
    );

    // When S1=1, Y is a 2:1 mux between C and D selected by S0.
    check_when_S1_high_2to1_CD: assert property (
        @(posedge CLK) (S1 == 1'b1) |-> (Y == (S0 ? D : C))
    );

    // When S0=0, Y is a 2:1 mux between A and C selected by S1.
    check_when_S0_low_2to1_AC: assert property (
        @(posedge CLK) (S0 == 1'b0) |-> (Y == (S1 ? C : A))
    );

    // When S0=1, Y is a 2:1 mux between B and D selected by S1.
    check_when_S0_high_2to1_BD: assert property (
        @(posedge CLK) (S0 == 1'b1) |-> (Y == (S1 ? D : B))
    );
endmodule