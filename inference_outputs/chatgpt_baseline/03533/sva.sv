module my_module_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic B2,
    input logic X
);

    wire A2_A3;
    assign A2_A3 = A2 & ~A3;

    // X must match the implemented combinational equation.
    check_x_matches_equation: assert property (
        @($global_clock) X == ((A1 | A2_A3) & B1)
    );

    // B1 low forces the output low.
    check_b1_low_forces_x_low: assert property (
        @($global_clock) !B1 |-> !X
    );

    // A1 drives X high when B1 is high.
    check_a1_path_sets_x: assert property (
        @($global_clock) (A1 && B1) |-> X
    );

    // The A2 & ~A3 term drives X high when A1 is low and B1 is high.
    check_a2_a3_path_sets_x: assert property (
        @($global_clock) (B1 && !A1 && A2 && !A3) |-> X
    );

    // If neither A1 nor A2 & ~A3 is active, X must be low when B1 is high.
    check_no_active_path_sets_x_low: assert property (
        @($global_clock) (B1 && !A1 && (!A2 || A3)) |-> !X
    );

endmodule