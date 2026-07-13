module MUX2X1_sva (
    input logic CLK,    // External sampling clock; RTL has no clock/reset (purely combinational)
    input logic A,
    input logic B,
    input logic S,
    input logic Y
);
    // MUX2 truth table: when S=0, Y=A.
    check_mux2_sel0_A: assert property (
        @(posedge CLK) (S == 1'b0) |=> (Y == A)
    );
    // MUX2 truth table: when S=1, Y=B.
    check_mux2_sel1_B: assert property (
        @(posedge CLK) (S == 1'b1) |=> (Y == B)
    );
    // Functional equation: Y = (~S & A) | (S & B).
    check_mux2_functional_eq: assert property (
        @(posedge CLK) Y == ((~S & A) | (S & B))
    );
    // If A and B are equal, Y must equal that value regardless of S.
    check_mux2_equal_inputs_hold: assert property (
        @(posedge CLK) (A == B) |=> (Y == A)
    );
endmodule

module MUX4X1_sva (
    input logic CLK,    // External sampling clock; RTL has no clock/reset (purely combinational)
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic S0,
    input logic S1,
    input logic Y
);
    // Functional equation: Y = S1 ? (S0 ? D : C) : (S0 ? B : A).
    check_mux4_functional_eq: assert property (
        @(posedge CLK) Y == (S1 ? (S0 ? D : C) : (S0 ? B : A))
    );
    // Truth table: S1=0,S0=0 selects A.
    check_mux4_sel00_A: assert property (
        @(posedge CLK) ((S1 == 1'b0) && (S0 == 1'b0)) |=> (Y == A)
    );
    // Truth table: S1=0,S0=1 selects B.
    check_mux4_sel01_B: assert property (
        @(posedge CLK) ((S1 == 1'b0) && (S0 == 1'b1)) |=> (Y == B)
    );
    // Truth table: S1=1,S0=0 selects C.
    check_mux4_sel10_C: assert property (
        @(posedge CLK) ((S1 == 1'b1) && (S0 == 1'b0)) |=> (Y == C)
    );
    // Truth table: S1=1,S0=1 selects D.
    check_mux4_sel11_D: assert property (
        @(posedge CLK) ((S1 == 1'b1) && (S0 == 1'b1)) |=> (Y == D)
    );
    // Grouping by first stage: when S0=0, Y = (S1 ? C : A).
    check_mux4_grouping_S0_0: assert property (
        @(posedge CLK) (S0 == 1'b0) |=> (Y == (S1 ? C : A))
    );
    // Grouping by first stage: when S0=1, Y = (S1 ? D : B).
    check_mux4_grouping_S0_1: assert property (
        @(posedge CLK) (S0 == 1'b1) |=> (Y == (S1 ? D : B))
    );
    // If all data inputs are equal, Y must equal that value regardless of selects.
    check_mux4_all_equal_passthrough: assert property (
        @(posedge CLK) ((A == B) && (B == C) && (C == D)) |=> (Y == A)
    );
    // If S1=0 and A==B, Y must equal A regardless of S0.
    check_mux4_equal_pair_lowbank: assert property (
        @(posedge CLK) ((S1 == 1'b0) && (A == B)) |=> (Y == A)
    );
    // If S1=1 and C==D, Y must equal C regardless of S0.
    check_mux4_equal_pair_highbank: assert property (
        @(posedge CLK) ((S1 == 1'b1) && (C == D)) |=> (Y == C)
    );
endmodule