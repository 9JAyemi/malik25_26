module adder_subtractor_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic       SUB,
    input logic [3:0] out
);

    // Out must match the selected arithmetic operation.
    check_selected_operation: assert property (
        @($global_clock) (out == (SUB ? (in0 - in1) : (in0 + in1)))
    );

    // When SUB is low, out must be the 4-bit sum of in0 and in1.
    check_add_mode: assert property (
        @($global_clock) (!SUB) |-> (out == (in0 + in1))
    );

    // When SUB is high, out must be the 4-bit difference of in0 and in1.
    check_subtract_mode: assert property (
        @($global_clock) SUB |-> (out == (in0 - in1))
    );

    // A zero second operand must leave in0 unchanged.
    check_zero_second_operand: assert property (
        @($global_clock) (in1 == 4'd0) |-> (out == in0)
    );

    // Subtracting equal operands must produce zero.
    check_equal_operands_subtract: assert property (
        @($global_clock) (SUB && (in0 == in1)) |-> (out == 4'd0)
    );

endmodule