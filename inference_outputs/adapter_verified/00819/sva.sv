module and4_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);

// X must equal the AND of all four inputs.
    check_x_matches_and4: assert property (
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

// All four high drive X high.
    check_all_high_drives_x_high: assert property (
        @(posedge clk) (A & B & C & D) |-> X
    );

endmodule
