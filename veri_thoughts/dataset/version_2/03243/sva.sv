module and_gate_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y
);

    // External clk samples this combinational DUT; the RTL has no reset.

    // Y matches the implemented AND of the four inverted inputs.
    check_output_function: assert property (
        @(posedge clk) Y == ((~A) & (~B) & (~C) & (~D))
    );

    // All inputs low must drive Y high.
    check_all_low_drives_y_high: assert property (
        @(posedge clk) (!A && !B && !C && !D) |-> Y
    );

    // Y high means all inputs are low.
    check_y_high_requires_all_low: assert property (
        @(posedge clk) Y |-> (!A && !B && !C && !D)
    );

    // Y low means at least one input is high.
    check_y_low_requires_some_input_high: assert property (
        @(posedge clk) (!Y) |-> (A || B || C || D)
    );

    // A high forces Y low.
    check_a_high_forces_y_low: assert property (
        @(posedge clk) A |-> !Y
    );

    // B high forces Y low.
    check_b_high_forces_y_low: assert property (
        @(posedge clk) B |-> !Y
    );

    // C high forces Y low.
    check_c_high_forces_y_low: assert property (
        @(posedge clk) C |-> !Y
    );

    // D high forces Y low.
    check_d_high_forces_y_low: assert property (
        @(posedge clk) D |-> !Y
    );

endmodule