module and4b_sva (
    input logic clk,
    input logic A_N,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);

    // X must equal the inverted OR of all inputs.
    check_functional_equivalence: assert property (
        @(posedge clk) X == ~(A_N | B | C | D)
    );

    // All inputs low must drive X high.
    check_all_inputs_low_drives_x_high: assert property (
        @(posedge clk) (!A_N && !B && !C && !D) |-> X
    );

    // A_N high must force X low.
    check_a_n_high_forces_x_low: assert property (
        @(posedge clk) A_N |-> !X
    );

    // B high must force X low.
    check_b_high_forces_x_low: assert property (
        @(posedge clk) B |-> !X
    );

    // C high must force X low.
    check_c_high_forces_x_low: assert property (
        @(posedge clk) C |-> !X
    );

    // D high must force X low.
    check_d_high_forces_x_low: assert property (
        @(posedge clk) D |-> !X
    );

    // X high implies all inputs are low.
    check_x_high_implies_all_inputs_low: assert property (
        @(posedge clk) X |-> (!A_N && !B && !C && !D)
    );

    // X low implies at least one input is high.
    check_x_low_implies_some_input_high: assert property (
        @(posedge clk) !X |-> (A_N || B || C || D)
    );

endmodule