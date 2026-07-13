module bitwise_op_sva (
    input logic [15:0] in1,
    input logic [15:0] in2,
    input logic [15:0] in3,
    input logic [15:0] in4,
    input logic        reset,
    input logic [15:0] out1,
    input logic [15:0] out2
);

    // No explicit RTL clock; sample on the formal global clock.
    // reset is active high and the RTL is purely combinational.

    // Reset forces both outputs to zero.
    check_reset_clears_outputs: assert property (
        @($global_clock) reset |-> ((out1 == 16'h0000) && (out2 == 16'h0000))
    );

    // Outside reset, out1 is the bitwise AND of in1 and in2.
    check_out1_bitwise_and: assert property (
        @($global_clock) disable iff (reset) (out1 == (in1 & in2))
    );

    // Outside reset, out2 is the bitwise XOR of in3 and in4.
    check_out2_bitwise_xor: assert property (
        @($global_clock) disable iff (reset) (out2 == (in3 ^ in4))
    );

    // Outside reset, a zero AND operand forces out1 to zero.
    check_out1_zero_when_operand_zero: assert property (
        @($global_clock) disable iff (reset)
        ((in1 == 16'h0000) || (in2 == 16'h0000)) |-> (out1 == 16'h0000)
    );

    // Outside reset, an all-ones AND operand passes the other operand through.
    check_out1_passthrough_when_operand_all_ones: assert property (
        @($global_clock) disable iff (reset)
        ((in1 == 16'hFFFF) || (in2 == 16'hFFFF)) |->
        (((in1 != 16'hFFFF) || (out1 == in2)) &&
         ((in2 != 16'hFFFF) || (out1 == in1)))
    );

    // Outside reset, equal XOR operands force out2 to zero.
    check_out2_zero_when_operands_equal: assert property (
        @($global_clock) disable iff (reset)
        (in3 == in4) |-> (out2 == 16'h0000)
    );

    // Outside reset, a zero XOR operand passes the other operand through.
    check_out2_passthrough_when_operand_zero: assert property (
        @($global_clock) disable iff (reset)
        ((in3 == 16'h0000) || (in4 == 16'h0000)) |->
        (((in3 != 16'h0000) || (out2 == in4)) &&
         ((in4 != 16'h0000) || (out2 == in3)))
    );

endmodule