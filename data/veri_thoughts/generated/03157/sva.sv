module sub4_sva (
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] out1,
    input logic [3:0] out2
);

    // out1 must always equal the 4-bit difference in1 minus in2.
    check_out1_subtract: assert property (
        @($global_clock) out1 == (in1 - in2)
    );

    // out2 must always equal the 4-bit difference in2 minus in1.
    check_out2_subtract: assert property (
        @($global_clock) out2 == (in2 - in1)
    );

    // The two outputs must sum to zero modulo 16.
    check_outputs_add_to_zero: assert property (
        @($global_clock) (out1 + out2) == 4'h0
    );

    // Equal inputs must produce zero on both outputs.
    check_equal_inputs_zero_outputs: assert property (
        @($global_clock) (in1 == in2) |-> (out1 == 4'h0 && out2 == 4'h0)
    );

endmodule