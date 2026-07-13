module my_module_sva (
    input logic in1,
    input logic in2,
    input logic in3,
    input logic out1
);

    // No RTL clock or reset is present; sample on the global formal clock.

    // out1 follows the composed combinational logic of the DUT.
    check_out1_function: assert property (
        @($global_clock) out1 == ((~((in1 & in2) | in3)) & ~in3)
    );

    // A high in3 forces out1 low.
    check_in3_forces_low: assert property (
        @($global_clock) in3 |-> (out1 == 1'b0)
    );

    // High in1 and in2 force out1 low.
    check_in1_in2_force_low: assert property (
        @($global_clock) (in1 && in2) |-> (out1 == 1'b0)
    );

    // With in3 low and in1 low, out1 must be high.
    check_in3_low_in1_low_gives_high: assert property (
        @($global_clock) (!in3 && !in1) |-> (out1 == 1'b1)
    );

    // With in3 low and in2 low, out1 must be high.
    check_in3_low_in2_low_gives_high: assert property (
        @($global_clock) (!in3 && !in2) |-> (out1 == 1'b1)
    );

    // A high out1 implies in3 is low and in1/in2 are not both high.
    check_out1_high_implies_input_conditions: assert property (
        @($global_clock) out1 |-> (!in3 && !(in1 && in2))
    );

endmodule