module logic_gate_assertions (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic VPWR,
    input logic VGND
);

    // Y must match the RTL equation.
    check_y_matches_rtl_equation: assert property (
        @(posedge clk)
        Y == (((A1 & A2 & A3) | (A1 & ~B1) | (~A1 & B1) | (~A1 & ~A2 & ~A3 & B1)) ? 1'b1 : 1'b0)
    );

    // With A1 low, Y must follow B1.
    check_a1_low_y_follows_b1: assert property (
        @(posedge clk)
        (A1 == 1'b0) |-> (Y == B1)
    );

    // With A1 high and B1 low, Y must be high.
    check_a1_high_b1_low_y_high: assert property (
        @(posedge clk)
        ((A1 == 1'b1) && (B1 == 1'b0)) |-> (Y == 1'b1)
    );

    // With A1 high and B1 high, Y must equal A2 & A3.
    check_a1_high_b1_high_y_equals_a2_and_a3: assert property (
        @(posedge clk)
        ((A1 == 1'b1) && (B1 == 1'b1)) |-> (Y == (A2 & A3))
    );

    // With A1 and B1 low, Y must be low.
    check_a1_low_b1_low_y_low: assert property (
        @(posedge clk)
        ((A1 == 1'b0) && (B1 == 1'b0)) |-> (Y == 1'b0)
    );

    // With A1 and B1 high and A2 low, Y must be low.
    check_a1_b1_high_a2_low_y_low: assert property (
        @(posedge clk)
        ((A1 == 1'b1) && (B1 == 1'b1) && (A2 == 1'b0)) |-> (Y == 1'b0)
    );

    // With A1 and B1 high and A3 low, Y must be low.
    check_a1_b1_high_a3_low_y_low: assert property (
        @(posedge clk)
        ((A1 == 1'b1) && (B1 == 1'b1) && (A3 == 1'b0)) |-> (Y == 1'b0)
    );

    // With A1, B1, A2, and A3 high, Y must be high.
    check_a1_b1_a2_a3_high_y_high: assert property (
        @(posedge clk)
        ((A1 == 1'b1) && (B1 == 1'b1) && (A2 == 1'b1) && (A3 == 1'b1)) |-> (Y == 1'b1)
    );

endmodule