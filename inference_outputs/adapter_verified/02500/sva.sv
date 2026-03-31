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
    check_a_n_forces_low: assert property (
        @(posedge clk) A_N |-> !Y
    );

// B_N high forces Y low.
    check_b_n_forces_low: assert property (
        @(posedge clk) B_N |-> !Y
    );

// C low forces Y low.
    check_c_low_forces_low: assert property (
        @(posedge clk) !C |-> !Y
    );

// D low forces Y low.
    check_d_low_forces_low: assert property (
        @(posedge clk) !D |-> !Y
    );

// With all active inputs high, Y is high.
    check_all_active_inputs_drive_high: assert property (
        @(posedge clk) (!A_N && !B_N && C && D) |-> Y
    );

// A_N and B_N high together force Y low.
    check_a_n_and_b_n_force_low: assert property (
        @(posedge clk) (A_N && B_N) |-> !Y
    );

// A_N and C low together force Y low.
    check_a_n_and_c_low_force_low: assert property (
        @(posedge clk) (A_N && !C) |-> !Y
    );

// A_N and D low together force Y low.
    check_a_n_and_d_low_force_low: assert property (
        @(posedge clk) (A_N && !D) |-> !Y
    );

// B_N and C low together force Y low.
    check_b_n_and_c_low_force_low: assert property (
        @(posedge clk) (B_N && !C) |-> !Y
    );

// B_N and D low together force Y low.
    check_b_n_and_d_low_force_low: assert property (
        @(posedge clk) (B_N && !D) |-> !Y
    );

endmodule
