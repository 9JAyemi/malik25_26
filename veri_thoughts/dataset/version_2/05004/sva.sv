module karnaugh_map_4_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic F
);

    // F matches the implemented Boolean function and does not depend on A.
    check_function_equation: assert property (
        @($global_clock) F == ((B & ~C) | (B & D) | (~B & C & ~D))
    );

    // When B and C are both low, F is low.
    check_bc_00_forces_zero: assert property (
        @($global_clock) (~B & ~C) |-> (F == 1'b0)
    );

    // When B is low, C is high, and D is low, F is high.
    check_b0_c1_d0_sets_one: assert property (
        @($global_clock) (~B & C & ~D) |-> (F == 1'b1)
    );

    // When B is low, C is high, and D is high, F is low.
    check_b0_c1_d1_sets_zero: assert property (
        @($global_clock) (~B & C & D) |-> (F == 1'b0)
    );

    // When B is high and C is low, F is high regardless of D.
    check_b1_c0_forces_one: assert property (
        @($global_clock) (B & ~C) |-> (F == 1'b1)
    );

    // When B and C are high and D is low, F is low.
    check_b1_c1_d0_sets_zero: assert property (
        @($global_clock) (B & C & ~D) |-> (F == 1'b0)
    );

    // When B, C, and D are all high, F is high.
    check_b1_c1_d1_sets_one: assert property (
        @($global_clock) (B & C & D) |-> (F == 1'b1)
    );

endmodule