module mux4_1_sva (
    input logic clk,
    input logic Y,
    input logic D0,
    input logic D1,
    input logic D2,
    input logic D3,
    input logic S0,
    input logic S1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

// Y matches the RTL mux network for all S values.
    check_full_mux_function: assert property (
        @(posedge clk) disable iff (1'b0)
        Y == ((S1 == 1'b0) ? ((S0 == 1'b0) ? D0 : D1) : ((S0 == 1'b0) ? D2 : D3))
    );

// When S1 is low, Y selects between D0 and D1 on S0.
    check_low_s1_select: assert property (
        @(posedge clk) disable iff (1'b0)
        (S1 == 1'b0) |-> (Y == ((S0 == 1'b0) ? D0 : D1))
    );

// When S1 is high, Y selects between D2 and D3 on S0.
    check_high_s1_select: assert property (
        @(posedge clk) disable iff (1'b0)
        (S1 == 1'b1) |-> (Y == ((S0 == 1'b0) ? D2 : D3))
    );

// With S1 low and S0 low, Y follows D0.
    check_low_s1_low_s0_selects_d0: assert property (
        @(posedge clk) disable iff (1'b0)
        (S1 == 1'b0 && S0 == 1'b0) |-> (Y == D0)
    );

// With S1 low and S0 high, Y follows D1.
    check_low_s1_high_s0_selects_d1: assert property (
        @(posedge clk) disable iff (1'b0)
        (S1 == 1'b0 && S0 == 1'b1) |-> (Y == D1)
    );

// With S1 high and S0 low, Y follows D2.
    check_high_s1_low_s0_selects_d2: assert property (
        @(posedge clk) disable iff (1'b0)
        (S1 == 1'b1 && S0 == 1'b0) |-> (Y == D2)
    );

// With S1 high and S0 high, Y follows D3.
    check_high_s1_high_s0_selects_d3: assert property (
        @(posedge clk) disable iff (1'b0)
        (S1 == 1'b1 && S0 == 1'b1) |-> (Y == D3)
    );

endmodule
