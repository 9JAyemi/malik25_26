module mux4_assertions (
    input logic in0,
    input logic in1,
    input logic sel0,
    input logic sel1,
    input logic out
);

    // No explicit clock or reset in the RTL; sample combinational behavior on the global clock.

    // Output matches the implemented boolean function.
    check_out_function: assert property (
        @($global_clock)
        out == ((in0 & ((~sel0) | sel1)) | (in1 & (sel0 | (~sel1))))
    );

    // When both selects are low, output is the OR of both inputs.
    check_sel_00_or_behavior: assert property (
        @($global_clock)
        (!sel0 && !sel1) |-> (out == (in0 | in1))
    );

    // When sel0 is low and sel1 is high, output follows in0.
    check_sel_01_in0_behavior: assert property (
        @($global_clock)
        (!sel0 && sel1) |-> (out == in0)
    );

    // When sel0 is high and sel1 is low, output follows in1.
    check_sel_10_in1_behavior: assert property (
        @($global_clock)
        (sel0 && !sel1) |-> (out == in1)
    );

    // When both selects are high, output is the OR of both inputs.
    check_sel_11_or_behavior: assert property (
        @($global_clock)
        (sel0 && sel1) |-> (out == (in0 | in1))
    );

    // If both inputs are low, output must be low.
    check_zero_inputs_drive_zero: assert property (
        @($global_clock)
        (!in0 && !in1) |-> (out == 1'b0)
    );

    // If both inputs are high, output must be high.
    check_one_inputs_drive_one: assert property (
        @($global_clock)
        (in0 && in1) |-> (out == 1'b1)
    );

    // If both inputs are equal, output matches that common value.
    check_equal_inputs_pass_through: assert property (
        @($global_clock)
        (in0 == in1) |-> (out == in0)
    );

endmodule