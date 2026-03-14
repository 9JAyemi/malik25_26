module tkg_c1u1_sva (
    input logic o,
    input logic s0,
    input logic [1:0] u0
);
    // No clock/reset in DUT; sample assertions on $global_clock.

    // Output matches the 2:1 mux function of s0 and u0.
    check_mux_function: assert property (
        @($global_clock) o == (s0 ? u0[0] : u0[1])
    );

    // When s0 is 1, output equals u0[0].
    check_true_select: assert property (
        @($global_clock) s0 |-> (o == u0[0])
    );

    // When s0 is 0, output equals u0[1].
    check_false_select: assert property (
        @($global_clock) !s0 |-> (o == u0[1])
    );

    // If both inputs are equal, output equals that common value.
    check_equal_inputs_force: assert property (
        @($global_clock) (u0[0] == u0[1]) |-> (o == u0[0])
    );

    // If s0 and u0 are stable across cycles, o remains stable.
    check_output_stability: assert property (
        @($global_clock) $stable({s0,u0}) |-> $stable(o)
    );
endmodule