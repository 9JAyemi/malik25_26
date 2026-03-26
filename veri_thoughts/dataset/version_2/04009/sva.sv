module add_sub_16bit_sva (
    input logic        clk,
    input logic [15:0] minuend,
    input logic [15:0] subtrahend,
    input logic        control,
    input logic [15:0] result
);

    // Add mode outputs the 16-bit sum.
    check_add_mode_function: assert property (
        @(posedge clk) !control |-> (result == (minuend + subtrahend))
    );

    // Subtract mode adds the 16-bit two's complement of subtrahend.
    check_sub_mode_function: assert property (
        @(posedge clk) control |-> (result == (minuend + ((~subtrahend) + 16'h0001)))
    );

    // Adding zero leaves the minuend unchanged.
    check_add_zero_subtrahend_identity: assert property (
        @(posedge clk) (!control && (subtrahend == 16'h0000)) |-> (result == minuend)
    );

    // Subtracting zero leaves the minuend unchanged.
    check_sub_zero_subtrahend_identity: assert property (
        @(posedge clk) (control && (subtrahend == 16'h0000)) |-> (result == minuend)
    );

    // With zero minuend in add mode, result matches subtrahend.
    check_add_zero_minuend_passthrough: assert property (
        @(posedge clk) (!control && (minuend == 16'h0000)) |-> (result == subtrahend)
    );

    // Subtracting equal operands produces zero.
    check_sub_equal_operands_zero: assert property (
        @(posedge clk) (control && (minuend == subtrahend)) |-> (result == 16'h0000)
    );

    // With zero minuend in subtract mode, result is the two's complement of subtrahend.
    check_sub_zero_minuend_twos_complement: assert property (
        @(posedge clk) (control && (minuend == 16'h0000)) |-> (result == ((~subtrahend) + 16'h0001))
    );

endmodule