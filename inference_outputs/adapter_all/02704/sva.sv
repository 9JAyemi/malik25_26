module sky130_fd_sc_ms__nor3b_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C_N
);

    // Y matches the implemented NOR-AND function.
    check_function_equivalence: assert property (
        @(posedge clk) Y == (C_N & ~(A | B))
    );

    // A high forces the NOR output low, so Y must be low.
    check_a_high_forces_y_low: assert property (
        @(posedge clk) A |-> !Y
    );

    // B high forces the NOR output low, so Y must be low.
    check_b_high_forces_y_low: assert property (
        @(posedge clk) B |-> !Y
    );

    // C_N low forces the AND output low, so Y must be low.
    check_c_n_low_forces_y_low: assert property (
        @(posedge clk) !C_N |-> !Y
    );

    // With all active inputs low, Y must be high.
    check_all_inputs_inactive_drive_y_high: assert property (
        @(posedge clk) (!A && !B && C_N) |-> Y
    );

    // Y high requires C_N to be high and both NOR inputs to be low.
    check_y_high_requires_active_c_n_and_inactive_nor_inputs: assert property (
        @(posedge clk) Y |-> (C_N && !A && !B)
    );

endmodule