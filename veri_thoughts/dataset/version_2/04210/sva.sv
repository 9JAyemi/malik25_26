module comparator_sva (
    input logic [1:0] in1,
    input logic [1:0] in2,
    input logic out
);

    // When in1 is greater than in2, out must be high.
    check_out_high_when_in1_greater: assert property (
        @($global_clock) (in1 > in2) |-> (out == 1'b1)
    );

    // When in1 equals in2, out must be low.
    check_out_low_when_inputs_equal: assert property (
        @($global_clock) (in1 == in2) |-> (out == 1'b0)
    );

    // When in1 is less than in2, out must be low.
    check_out_low_when_in1_less: assert property (
        @($global_clock) (in1 < in2) |-> (out == 1'b0)
    );

endmodule