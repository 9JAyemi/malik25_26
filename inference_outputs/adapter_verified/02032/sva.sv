module sky130_fd_sc_ms__o21ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

// Y matches the implemented OR-then-NAND function.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ~(B1 & (A1 | A2))
    );

// B1 low forces Y high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) !B1 |-> Y
    );

// A1 high with B1 high forces Y low.
    check_a1_high_with_b1_high_forces_y_low: assert property (
        @(posedge clk) (B1 && A1) |-> !Y
    );

// A2 high with B1 high forces Y low.
    check_a2_high_with_b1_high_forces_y_low: assert property (
        @(posedge clk) (B1 && A2) |-> !Y
    );

// Y high implies B1 is low or both A inputs are low.
    check_y_high_implies_cause: assert property (
        @(posedge clk) Y |-> (!B1 || (!A1 && !A2))
    );

// Y low implies B1 is high and at least one A input is high.
    check_y_low_implies_cause: assert property (
        @(posedge clk) !Y |-> (B1 && (A1 || A2))
    );

endmodule
