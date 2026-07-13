module sky130_fd_sc_lp__and4_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

// X must equal the 4-input AND of A, B, C, and D.
    check_and_function: assert property (
        @(posedge clk) X == (A & B & C & D)
    );

// A low forces X low.
    check_a_low_forces_x_low: assert property (
        @(posedge clk) !A |-> !X
    );

// B low forces X low.
    check_b_low_forces_x_low: assert property (
        @(posedge clk) !B |-> !X
    );

// C low forces X low.
    check_c_low_forces_x_low: assert property (
        @(posedge clk) !C |-> !X
    );

// D low forces X low.
    check_d_low_forces_x_low: assert property (
        @(posedge clk) !D |-> !X
    );

// All inputs high drive X high.
    check_all_high_drives_x_high: assert property (
        @(posedge clk) (A & B & C & D) |-> X
    );

// X high implies all inputs are high.
    check_x_high_implies_all_high: assert property (
        @(posedge clk) X |-> (A & B & C & D)
    );

endmodule
