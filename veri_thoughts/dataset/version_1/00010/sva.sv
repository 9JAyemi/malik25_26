module xor_reset_sva (
    input logic in1,
    input logic in2,
    input logic reset,
    input logic out1
);

    // Reset forces the output low.
    check_reset_forces_zero: assert property (
        @($global_clock) reset |-> (out1 == 1'b0)
    );

    // Outside reset, the output matches in1 XOR in2.
    check_xor_function: assert property (
        @($global_clock) disable iff (reset) (out1 == (in1 ^ in2))
    );

    // Outside reset, 0 XOR 0 drives the output low.
    check_xor_00_case: assert property (
        @($global_clock) disable iff (reset)
            (((in1 == 1'b0) && (in2 == 1'b0)) |-> (out1 == 1'b0))
    );

    // Outside reset, 0 XOR 1 drives the output high.
    check_xor_01_case: assert property (
        @($global_clock) disable iff (reset)
            (((in1 == 1'b0) && (in2 == 1'b1)) |-> (out1 == 1'b1))
    );

    // Outside reset, 1 XOR 0 drives the output high.
    check_xor_10_case: assert property (
        @($global_clock) disable iff (reset)
            (((in1 == 1'b1) && (in2 == 1'b0)) |-> (out1 == 1'b1))
    );

    // Outside reset, 1 XOR 1 drives the output low.
    check_xor_11_case: assert property (
        @($global_clock) disable iff (reset)
            (((in1 == 1'b1) && (in2 == 1'b1)) |-> (out1 == 1'b0))
    );

endmodule