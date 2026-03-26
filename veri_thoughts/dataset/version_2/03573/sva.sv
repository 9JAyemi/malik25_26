module mux_2_1_en_assertions(
    input logic in0,
    input logic in1,
    input logic en,
    input logic out
);

    // Output always matches the mux select function.
    check_mux_function: assert property (
        @($global_clock) out == (en ? in1 : in0)
    );

    // When en is high, output follows in1.
    check_select_in1: assert property (
        @($global_clock) en |-> (out == in1)
    );

    // When en is low, output follows in0.
    check_select_in0: assert property (
        @($global_clock) !en |-> (out == in0)
    );

    // If both inputs are equal, output matches that common value.
    check_equal_inputs: assert property (
        @($global_clock) (in0 == in1) |-> (out == in0)
    );

endmodule