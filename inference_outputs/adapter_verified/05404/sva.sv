module sky130_fd_sc_hvl__a22oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

// Y matches the implemented NAND-AND function.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ((~A1 & ~A2) & (~B1 & ~B2))
    );

// All four high inputs drive Y high.
    check_all_high_drives_y_high: assert property (
        @(posedge clk) (A1 && A2 && B1 && B2) |-> Y
    );

// A1 high with A2 low forces Y low.
    check_a1_high_a2_low_drives_y_low: assert property (
        @(posedge clk) (A1 && !A2) |-> !Y
    );

// A2 high with A1 low forces Y low.
    check_a2_high_a1_low_drives_y_low: assert property (
        @(posedge clk) (A2 && !A1) |-> !Y
    );

// B1 high with B2 low forces Y low.
    check_b1_high_b2_low_drives_y_low: assert property (
        @(posedge clk) (B1 && !B2) |-> !Y
    );

// B2 high with B1 low forces Y low.
    check_b2_high_b1_low_drives_y_low: assert property (
        @(posedge clk) (B2 && !B1) |-> !Y
    );

// Y high implies all four inputs are high.
    check_y_high_requires_all_high: assert property (
        @(posedge clk) Y |-> (A1 && A2 && B1 && B2)
    );

// Y low implies at least one input is low.
    check_y_low_requires_some_low: assert property (
        @(posedge clk) !Y |-> (!A1 || !A2 || !B1 || !B2)
    );

endmodule
