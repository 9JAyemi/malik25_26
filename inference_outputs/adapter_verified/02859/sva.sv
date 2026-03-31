module and4bb_sva (
    input logic clk,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D,
    input logic X
);

// X must equal the AND of A_N, B_N, C, and D.
    check_function_equivalence: assert property (
        @(posedge clk) X == (A_N & B_N & C & D)
    );

// A_N low forces X low.
    check_a_n_low_forces_x_low: assert property (
        @(posedge clk) !A_N |-> !X
    );

// B_N low forces X low.
    check_b_n_low_forces_x_low: assert property (
        @(posedge clk) !B_N |-> !X
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
    check_all_inputs_high_drive_x_high: assert property (
        @(posedge clk) (A_N && B_N && C && D) |-> X
    );

// X high implies all inputs are high.
    check_x_high_implies_all_inputs_high: assert property (
        @(posedge clk) X |-> (A_N && B_N && C && D)
    );

endmodule
