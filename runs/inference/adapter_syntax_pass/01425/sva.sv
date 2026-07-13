module sky130_fd_sc_lp__a311oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);

    // Y matches the implemented A3&A1&A2|~B1|~C1 function.
    check_y_function: assert property (
        @(posedge clk) Y == ((A3 & A1 & A2) | ~B1 | ~C1)
    );

    // B1 low forces Y high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) !B1 |-> Y
    );

    // C1 low forces Y high.
    check_c1_low_forces_y_high: assert property (
        @(posedge clk) !C1 |-> Y
    );

    // A1, A2, and A3 high force Y high.
    check_a3_a1_a2_high_force_y_high: assert property (
        @(posedge clk) (A3 & A1 & A2) |-> Y
    );

    // With B1 and C1 high, Y reduces to A3&A1&A2.
    check_bc_high_reduces_to_a3_a1_a2: assert property (
        @(posedge clk) (B1 & C1) |-> (Y == (A3 & A1 & A2))
    );

    // With B1 and A3&A1&A2 high, Y must be high.
    check_b1_and_a3_a1_a2_high_force_y_high: assert property (
        @(posedge clk) (B1 & A3 & A1 & A2) |-> Y
    );

    // With C1 and A3&A1&A2 high, Y must be high.
    check_c1_and_a3_a1_a2_high_force_y_high: assert property (
        @(posedge clk) (C1 & A3 & A1 & A2) |-> Y
    );

    // With B1 and C1 high, a low Y implies A3&A1&A2 is low.
    check_bc_high_and_y_low_implies_a3_a1_a2_low: assert property (
        @(posedge clk) (B1 & C1 & !Y) |-> !(A3 & A1 & A2)
    );

endmodule