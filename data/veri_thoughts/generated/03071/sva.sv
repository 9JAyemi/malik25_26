module adder_subtractor_sva (
    input logic clk,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic SUB,
    input logic [3:0] out
);

    // Stable sampled inputs must produce the selected 4-bit arithmetic result.
    check_selected_operation_result: assert property (
        @(posedge clk)
        (!$initstate && $stable({in0, in1, SUB})) |->
        (out == (SUB ? (in0 + (~in1 + 4'b0001)) : (in0 + in1)))
    );

    // With in1 at zero, both add and subtract modes must pass through in0.
    check_in1_zero_identity: assert property (
        @(posedge clk)
        (!$initstate && $stable({in0, in1, SUB}) && (in1 == 4'h0)) |->
        (out == in0)
    );

    // In add mode, zero on in0 must pass through in1.
    check_add_in0_zero_passthrough: assert property (
        @(posedge clk)
        (!$initstate && $stable({in0, in1, SUB}) && !SUB && (in0 == 4'h0)) |->
        (out == in1)
    );

    // In subtract mode, equal operands must produce zero.
    check_self_subtract_zero: assert property (
        @(posedge clk)
        (!$initstate && $stable({in0, in1, SUB}) && SUB && (in0 == in1)) |->
        (out == 4'h0)
    );

    // Add mode must wrap on 4-bit overflow.
    check_add_overflow_wrap: assert property (
        @(posedge clk)
        (!$initstate && $stable({in0, in1, SUB}) && !SUB && (in0 == 4'hF) && (in1 == 4'h1)) |->
        (out == 4'h0)
    );

    // Subtract mode must wrap on 4-bit underflow.
    check_sub_underflow_wrap: assert property (
        @(posedge clk)
        (!$initstate && $stable({in0, in1, SUB}) && SUB && (in0 == 4'h0) && (in1 == 4'h1)) |->
        (out == 4'hF)
    );

endmodule