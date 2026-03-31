module sky130_fd_sc_ls__a32oi_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2
);

// Y matches the implemented NAND/AND logic.
    check_y_matches_implemented_function: assert property (
        @(posedge clk) Y == ((~A1 & ~A2 & ~A3) & (~B1 & ~B2))
    );

// All A inputs high force Y low.
    check_a_triplet_forces_y_low: assert property (
        @(posedge clk) (A1 & A2 & A3) |-> !Y
    );

// All B inputs high force Y low.
    check_b_triplet_forces_y_low: assert property (
        @(posedge clk) (B1 & B2) |-> !Y
    );

// A low and B low together force Y high.
    check_a0_b0_forces_y_high: assert property (
        @(posedge clk) (!A1 & !A2 & !A3 & !B1 & !B2) |-> Y
    );

// A low and B high together force Y low.
    check_a0_b12_forces_y_low: assert property (
        @(posedge clk) (!A1 & !A2 & !A3 & B1 & B2) |-> !Y
    );

// A high and B low together force Y low.
    check_a12_b0_forces_y_low: assert property (
        @(posedge clk) (A1 & A2 & A3 & !B1 & !B2) |-> !Y
    );

// A high and B high together force Y low.
    check_a12_b12_forces_y_low: assert property (
        @(posedge clk) (A1 & A2 & A3 & B1 & B2) |-> !Y
    );

endmodule
