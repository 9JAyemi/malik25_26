module sky130_fd_sc_hvl__nand2_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic Y
);

// Y must implement the NAND of A and B.
    check_nand_function: assert property (
        @(posedge clk) Y == ~(A & B)
    );

// A low forces Y high.
    check_a_low_forces_y_high: assert property (
        @(posedge clk) !A |-> Y
    );

// B low forces Y high.
    check_b_low_forces_y_high: assert property (
        @(posedge clk) !B |-> Y
    );

// Both inputs high force Y low.
    check_both_high_force_y_low: assert property (
        @(posedge clk) (A && B) |-> !Y
    );

// A high and B low force Y high.
    check_a_high_b_low_force_y_high: assert property (
        @(posedge clk) (A && !B) |-> Y
    );

// A low and B high force Y high.
    check_a_low_b_high_force_y_high: assert property (
        @(posedge clk) (!A && B) |-> Y
    );

endmodule
