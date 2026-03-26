module xor_product_sva (
    input logic       clk,
    input logic       reset,
    input logic [7:0] in_1,
    input logic [7:0] in_2,
    input logic       select,
    input logic [7:0] xor_output,
    input logic [7:0] or_output
);

    // or_output is the two's complement of in_1 masked by in_2.
    check_or_output_function: assert property (
        @(posedge clk) disable iff (reset)
        or_output == (((~in_1) + 8'h01) & in_2)
    );

    // The same or_output function holds while reset is asserted.
    check_or_output_function_during_reset: assert property (
        @(posedge clk)
        reset |-> (or_output == (((~in_1) + 8'h01) & in_2))
    );

    // or_output can only set bits that are set in in_2.
    check_or_output_masks_in2: assert property (
        @(posedge clk) disable iff (reset)
        (or_output & ~in_2) == 8'h00
    );

    // A zero in_1 produces a zero two's complement and thus zero or_output.
    check_or_output_zero_when_in1_zero: assert property (
        @(posedge clk) disable iff (reset)
        (in_1 == 8'h00) |-> (or_output == 8'h00)
    );

    // A zero in_2 forces or_output low because it is the AND mask.
    check_or_output_zero_when_in2_zero: assert property (
        @(posedge clk) disable iff (reset)
        (in_2 == 8'h00) |-> (or_output == 8'h00)
    );

    // One cycle after reset, select=0 makes xor_output follow in_1.
    check_xor_output_after_reset_uses_in1: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(reset) && !select) |-> (xor_output == in_1)
    );

    // One cycle after reset, select=1 makes xor_output follow in_2.
    check_xor_output_after_reset_uses_in2: assert property (
        @(posedge clk) disable iff ($initstate)
        ($past(reset) && select) |-> (xor_output == in_2)
    );

    // Without a prior reset, select=0 uses the registered sum and in_1.
    check_xor_output_after_nonreset_uses_in1: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && !select) |-> (xor_output == (((($past(in_1) + $past(in_2)) & 8'hFF)) ^ in_1))
    );

    // Without a prior reset, select=1 uses the registered sum and in_2.
    check_xor_output_after_nonreset_uses_in2: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (!$past(reset) && select) |-> (xor_output == (((($past(in_1) + $past(in_2)) & 8'hFF)) ^ in_2))
    );

endmodule