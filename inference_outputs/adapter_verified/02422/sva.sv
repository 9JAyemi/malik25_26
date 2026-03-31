module sky130_fd_sc_hdll__nand4bb_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B_N,
    input logic C,
    input logic D
);

// Y matches the implemented NAND/OR/BUF function.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == ~(A_N | B_N | ~(C & D))
    );

// A_N high forces Y low.
    check_a_n_high_forces_y_low: assert property (
        @(posedge clk) A_N |-> !Y
    );

// B_N high forces Y low.
    check_b_n_high_forces_y_low: assert property (
        @(posedge clk) B_N |-> !Y
    );

// C low forces Y low.
    check_c_low_forces_y_low: assert property (
        @(posedge clk) !C |-> !Y
    );

// D low forces Y low.
    check_d_low_forces_y_low: assert property (
        @(posedge clk) !D |-> !Y
    );

// With all active inputs high, Y is high.
    check_all_active_inputs_drive_y_high: assert property (
        @(posedge clk) (!A_N && !B_N && C && D) |-> Y
    );

// Y high implies all active inputs are high.
    check_y_high_implies_all_active_inputs: assert property (
        @(posedge clk) Y |-> (!A_N && !B_N && C && D)
    );

endmodule
