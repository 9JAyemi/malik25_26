module sky130_fd_sc_ms__nor3b_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C_N
);

// Y matches the implemented NOR-AND function.
    check_functional_equivalence: assert property (
        @(posedge clk) Y == (C_N & ~(A | B))
    );

// A high forces Y low.
    check_a_high_forces_y_low: assert property (
        @(posedge clk) A |-> !Y
    );

// B high forces Y low.
    check_b_high_forces_y_low: assert property (
        @(posedge clk) B |-> !Y
    );

// C_N low forces Y low.
    check_c_n_low_forces_y_low: assert property (
        @(posedge clk) !C_N |-> !Y
    );

// With all three active inputs, Y is high.
    check_all_active_inputs_drive_y_high: assert property (
        @(posedge clk) (!A && !B && C_N) |-> Y
    );

// Y high implies all three active inputs are present.
    check_y_high_requires_all_active_inputs: assert property (
        @(posedge clk) Y |-> (!A && !B && C_N)
    );

endmodule
