module sky130_fd_sc_ms__nor3b_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C_N
);

    // Y matches the implemented NOR/AND/buffer function.
    check_output_function: assert property (
        @(posedge clk) Y == ((~A) & (~B) & C_N)
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

    // With both NOR inputs low and C_N high, Y must be high.
    check_active_inputs_drive_y_high: assert property (
        @(posedge clk) (!A && !B && C_N) |-> Y
    );

    // A high Y requires both NOR inputs low and C_N high.
    check_y_high_requires_active_inputs: assert property (
        @(posedge clk) Y |-> (!A && !B && C_N)
    );

endmodule