module barrel_shifter_sva (
    input logic        clk,
    input logic [15:0] IN,
    input logic        SHIFT,
    input logic        DIR,
    input logic [15:0] OUT
);

    // OUT always matches the implemented shift-or-pass-through function.
    check_output_matches_function: assert property (
        @(posedge clk)
        OUT == (SHIFT ? (DIR ? {IN[14:0], 1'b0} : {1'b0, IN[15:1]}) : IN)
    );

    // When SHIFT is low, OUT passes IN through unchanged.
    check_no_shift_passthrough: assert property (
        @(posedge clk)
        !SHIFT |-> (OUT == IN)
    );

    // When SHIFT and DIR are high, OUT is IN shifted left by one.
    check_left_shift_selected: assert property (
        @(posedge clk)
        SHIFT && DIR |-> (OUT == {IN[14:0], 1'b0})
    );

    // Left shift inserts a zero into the least-significant bit.
    check_left_shift_zero_fill: assert property (
        @(posedge clk)
        SHIFT && DIR |-> (OUT[0] == 1'b0)
    );

    // When SHIFT is high and DIR is low, OUT is IN shifted right by one.
    check_right_shift_selected: assert property (
        @(posedge clk)
        SHIFT && !DIR |-> (OUT == {1'b0, IN[15:1]})
    );

    // Right shift inserts a zero into the most-significant bit.
    check_right_shift_zero_fill: assert property (
        @(posedge clk)
        SHIFT && !DIR |-> (OUT[15] == 1'b0)
    );

endmodule