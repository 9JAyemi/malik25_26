module sky130_fd_sc_hs__nand2b_sva (
    input logic A_N,
    input logic B,
    input logic VPWR,
    input logic VGND,
    input logic Y
);
    // Y equals NAND of A_N and B when powered.
    check_y_matches_function: assert property (
        @(posedge A_N or posedge B) disable iff (!VPWR || VGND) Y == ~(A_N & B)
    );
    // If A_N is LOW, Y must be HIGH.
    check_y_high_when_an_low: assert property (
        @(posedge A_N or posedge B) disable iff (!VPWR || VGND) (A_N == 1'b0) |-> (Y == 1'b1)
    );
    // If B is LOW, Y must be HIGH.
    check_y_high_when_b_low: assert property (
        @(posedge A_N or posedge B) disable iff (!VPWR || VGND) (B == 1'b0) |-> (Y == 1'b1)
    );
    // If both A_N and B are HIGH, Y must be LOW.
    check_y_low_when_both_high: assert property (
        @(posedge A_N or posedge B) disable iff (!VPWR || VGND) (A_N && B) |-> (Y == 1'b0)
    );
    // If Y is LOW, both inputs are HIGH.
    check_zero_implies_both_high: assert property (
        @(posedge A_N or posedge B) disable iff (!VPWR || VGND) (Y == 1'b0) |-> (A_N && B)
    );
    // If Y is HIGH, at least one input is LOW.
    check_one_implies_either_low: assert property (
        @(posedge A_N or posedge B) disable iff (!VPWR || VGND) (Y == 1'b1) |-> (!A_N || !B)
    );
    // Rising A_N with B HIGH drives Y LOW.
    check_an_rise_b_high_y_low: assert property (
        @(posedge A_N or posedge B) disable iff (!VPWR || VGND) ($rose(A_N) && (B == 1'b1)) |-> (Y == 1'b0)
    );
    // Rising B with A_N HIGH drives Y LOW.
    check_b_rise_an_high_y_low: assert property (
        @(posedge A_N or posedge B) disable iff (!VPWR || VGND) ($rose(B) && (A_N == 1'b1)) |-> (Y == 1'b0)
    );
    // Rising A_N with B LOW keeps Y HIGH.
    check_an_rise_b_low_y_high: assert property (
        @(posedge A_N or posedge B) disable iff (!VPWR || VGND) ($rose(A_N) && (B == 1'b0)) |-> (Y == 1'b1)
    );
    // Rising B with A_N LOW keeps Y HIGH.
    check_b_rise_an_low_y_high: assert property (
        @(posedge A_N or posedge B) disable iff (!VPWR || VGND) ($rose(B) && (A_N == 1'b0)) |-> (Y == 1'b1)
    );
endmodule