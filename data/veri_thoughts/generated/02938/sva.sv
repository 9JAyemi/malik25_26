module mux_4_1_using_2_1_sva (
    // Sampling clock for assertions (RTL has no clock/reset)
    input logic CLK,

    // DUT ports
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic S0,
    input logic S1,
    input logic Y,

    // Internal RTL nets (present in mux_4_1_using_2_1)
    input logic m1_out,
    input logic m2_out
);
    // No clock or reset in RTL; purely combinational 4:1 mux built from 2:1 muxes.
    // Assertions sampled on CLK; no reset used in disable iff.

    // Y equals A when S1=0 and S0=0.
    select_00_y_eq_a: assert property (
        @(posedge CLK) disable iff (1'b0) (!S1 && !S0) |-> (Y == A)
    );

    // Y equals B when S1=0 and S0=1.
    select_01_y_eq_b: assert property (
        @(posedge CLK) disable iff (1'b0) (!S1 && S0) |-> (Y == B)
    );

    // Y equals C when S1=1 and S0=0.
    select_10_y_eq_c: assert property (
        @(posedge CLK) disable iff (1'b0) (S1 && !S0) |-> (Y == C)
    );

    // Y equals D when S1=1 and S0=1.
    select_11_y_eq_d: assert property (
        @(posedge CLK) disable iff (1'b0) (S1 && S0) |-> (Y == D)
    );

    // Y matches the full nested ternary of a 4:1 mux.
    y_matches_function: assert property (
        @(posedge CLK) disable iff (1'b0) (Y == (S1 ? (S0 ? D : C) : (S0 ? B : A)))
    );

    // When S1=0, output selects m1_out.
    y_follows_m1_when_s1_low: assert property (
        @(posedge CLK) disable iff (1'b0) (!S1) |-> (Y == m1_out)
    );

    // When S1=1, output selects m2_out.
    y_follows_m2_when_s1_high: assert property (
        @(posedge CLK) disable iff (1'b0) (S1) |-> (Y == m2_out)
    );

    // When S0=0, m1_out=A and m2_out=C.
    m1_m2_selects_when_s0_low: assert property (
        @(posedge CLK) disable iff (1'b0) (!S0) |-> ((m1_out == A) && (m2_out == C))
    );

    // When S0=1, m1_out=B and m2_out=D.
    m1_m2_selects_when_s0_high: assert property (
        @(posedge CLK) disable iff (1'b0) (S0) |-> ((m1_out == B) && (m2_out == D))
    );
endmodule