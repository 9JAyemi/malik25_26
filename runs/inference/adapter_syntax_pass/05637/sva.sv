module and4b_sva (
    input logic clk,
    input logic A_N,
    input logic B,
    input logic C,
    input logic D,
    input logic X
);

    // X must equal the RTL OR-of-ones function.
    check_x_matches_rtl_function: assert property (
        @(posedge clk) X == ~(A_N | B | C | D)
    );

    // A_N high forces X low.
    check_an_high_forces_x_low: assert property (
        @(posedge clk) A_N |-> !X
    );

    // B high forces X low.
    check_b_high_forces_x_low: assert property (
        @(posedge clk) B |-> !X
    );

    // C high forces X low.
    check_c_high_forces_x_low: assert property (
        @(posedge clk) C |-> !X
    );

    // D high forces X low.
    check_d_high_forces_x_low: assert property (
        @(posedge clk) D |-> !X
    );

    // All inputs low produce X high.
    check_all_inputs_low_produces_x_high: assert property (
        @(posedge clk) (!A_N && !B && !C && !D) |-> X
    );

    // X high implies all inputs are low.
    check_x_high_implies_all_inputs_low: assert property (
        @(posedge clk) X |-> (!A_N && !B && !C && !D)
    );

endmodule