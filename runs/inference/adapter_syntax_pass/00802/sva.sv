module my_or4b_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B,
    input logic C,
    input logic D_N
);

    // X matches the implemented OR-of-A/B/C and inverted D_N.
    check_function_equivalence: assert property (
        @(posedge clk) X == (A | B | C | ~D_N)
    );

    // A high forces X high.
    check_a_forces_x_high: assert property (
        @(posedge clk) A |-> X
    );

    // B high forces X high.
    check_b_forces_x_high: assert property (
        @(posedge clk) B |-> X
    );

    // C high forces X high.
    check_c_forces_x_high: assert property (
        @(posedge clk) C |-> X
    );

    // D_N low forces X high.
    check_dn_low_forces_x_high: assert property (
        @(posedge clk) !D_N |-> X
    );

    // All low inputs make X low.
    check_all_inputs_low_drive_x_low: assert property (
        @(posedge clk) (!A && !B && !C && D_N) |-> !X
    );

    // X low implies A, B, and C are low and D_N is high.
    check_x_low_implies_inputs_low: assert property (
        @(posedge clk) !X |-> (!A && !B && !C && D_N)
    );

endmodule