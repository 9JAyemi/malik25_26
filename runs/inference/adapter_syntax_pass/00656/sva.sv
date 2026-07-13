module or3_4_custom_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C
);

    // X must equal the OR of A, B, and C.
    check_or_function: assert property (
        @(posedge clk) X == (A | B | C)
    );

    // X must be low when all inputs are low.
    check_all_inputs_low: assert property (
        @(posedge clk) (!A && !B && !C) |-> !X
    );

    // X must be high when A is high.
    check_a_high_sets_x: assert property (
        @(posedge clk) A |-> X
    );

    // X must be high when B is high.
    check_b_high_sets_x: assert property (
        @(posedge clk) B |-> X
    );

    // X must be high when C is high.
    check_c_high_sets_x: assert property (
        @(posedge clk) C |-> X
    );

    // X must be low when only A is high.
    check_a_only_keeps_x_low: assert property (
        @(posedge clk) (A && !B && !C) |-> !X
    );

    // X must be low when only B is high.
    check_b_only_keeps_x_low: assert property (
        @(posedge clk) (!A && B && !C) |-> !X
    );

    // X must be low when only C is high.
    check_c_only_keeps_x_low: assert property (
        @(posedge clk) (!A && !B && C) |-> !X
    );

endmodule