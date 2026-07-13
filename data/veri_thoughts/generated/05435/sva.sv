module four_input_nand_gate_sva (
    input logic clk,
    input logic Y,
    input logic A_N,
    input logic B,
    input logic C,
    input logic D
);

    // Y matches the implemented invert-then-NAND function.
    check_output_function: assert property (
        @(posedge clk) Y == ~(D & C & B & ~A_N)
    );

    // A_N high forces the output high.
    check_a_n_high_forces_y_high: assert property (
        @(posedge clk) A_N |-> Y
    );

    // Any low data input forces the output high.
    check_any_low_data_input_forces_y_high: assert property (
        @(posedge clk) (!B || !C || !D) |-> Y
    );

    // A_N low with all other inputs high forces the output low.
    check_all_active_inputs_drive_y_low: assert property (
        @(posedge clk) (!A_N && B && C && D) |-> !Y
    );

    // A low output can only occur for the single active-input case.
    check_y_low_has_unique_cause: assert property (
        @(posedge clk) !Y |-> (!A_N && B && C && D)
    );

endmodule