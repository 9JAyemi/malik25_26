module sky130_fd_sc_lp__or2_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B
);

// X must equal A OR B.
    check_or_function: assert property (
        @(posedge clk) X == (A | B)
    );

// A high must drive X high.
    check_a_high_sets_x: assert property (
        @(posedge clk) A |-> X
    );

// B high must drive X high.
    check_b_high_sets_x: assert property (
        @(posedge clk) B |-> X
    );

// Both inputs low must drive X low.
    check_both_low_clear_x: assert property (
        @(posedge clk) (!A && !B) |-> !X
    );

// X low implies both inputs are low.
    check_x_low_implies_both_low: assert property (
        @(posedge clk) !X |-> (!A && !B)
    );

endmodule
