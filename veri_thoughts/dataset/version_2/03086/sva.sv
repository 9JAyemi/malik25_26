module mux_2_to_1_sva (
    input logic in_0,
    input logic in_1,
    input logic select,
    input logic out
);

    // When select is low, out must follow in_0.
    check_select_low_routes_in0: assert property (
        @($global_clock) (!select) |-> (out == in_0)
    );

    // When select is high, out must follow in_1.
    check_select_high_routes_in1: assert property (
        @($global_clock) select |-> (out == in_1)
    );

    // Out must always implement the 2:1 mux function.
    check_mux_function: assert property (
        @($global_clock) (out == (select ? in_1 : in_0))
    );

endmodule