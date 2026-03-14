module mux4to1_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic sel0,
    input logic sel1,
    input logic Y
);
    // No clock/reset in DUT; pure combinational 4:1 mux with sel1:sel0 selecting D,C,B,A.

    // Y matches the mux boolean equation at any input/select edge.
    check_functional_eq: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge sel0 or negedge sel0 or posedge sel1 or negedge sel1)
        Y == ((~sel1 & ~sel0 & A) | (~sel1 & sel0 & B) | (sel1 & ~sel0 & C) | (sel1 & sel0 & D))
    );

    // When sel1:sel0 == 2'b00, Y equals A.
    check_sel00_routes_A: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge sel0 or negedge sel0 or posedge sel1 or negedge sel1)
        (~sel1 & ~sel0) |-> (Y == A)
    );

    // When sel1:sel0 == 2'b01, Y equals B.
    check_sel01_routes_B: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge sel0 or negedge sel0 or posedge sel1 or negedge sel1)
        (~sel1 & sel0) |-> (Y == B)
    );

    // When sel1:sel0 == 2'b10, Y equals C.
    check_sel10_routes_C: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge sel0 or negedge sel0 or posedge sel1 or negedge sel1)
        (sel1 & ~sel0) |-> (Y == C)
    );

    // When sel1:sel0 == 2'b11, Y equals D.
    check_sel11_routes_D: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge sel0 or negedge sel0 or posedge sel1 or negedge sel1)
        (sel1 & sel0) |-> (Y == D)
    );

    // If sel1:sel0 == 2'b00 and Y is HIGH, then A must be HIGH.
    check_sel00_y_high_implies_a_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge sel0 or negedge sel0 or posedge sel1 or negedge sel1)
        ((~sel1 & ~sel0) && (Y == 1'b1)) |-> (A == 1'b1)
    );

    // If sel1:sel0 == 2'b01 and Y is HIGH, then B must be HIGH.
    check_sel01_y_high_implies_b_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge sel0 or negedge sel0 or posedge sel1 or negedge sel1)
        ((~sel1 & sel0) && (Y == 1'b1)) |-> (B == 1'b1)
    );

    // If sel1:sel0 == 2'b10 and Y is HIGH, then C must be HIGH.
    check_sel10_y_high_implies_c_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge sel0 or negedge sel0 or posedge sel1 or negedge sel1)
        ((sel1 & ~sel0) && (Y == 1'b1)) |-> (C == 1'b1)
    );

    // If sel1:sel0 == 2'b11 and Y is HIGH, then D must be HIGH.
    check_sel11_y_high_implies_d_high: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge sel0 or negedge sel0 or posedge sel1 or negedge sel1)
        ((sel1 & sel0) && (Y == 1'b1)) |-> (D == 1'b1)
    );

    // If sel1:sel0 == 2'b00 and A is LOW, Y must be LOW.
    check_sel00_a_low_implies_y_low: assert property (
        @(posedge A or negedge A or posedge B or negedge B or posedge C or negedge C or posedge D or negedge D or posedge sel0 or negedge sel0 or posedge sel1 or negedge sel1)
        ((~sel1 & ~sel0) && (A == 1'b0)) |-> (Y == 1'b0)
    );

endmodule