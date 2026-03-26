module top_module_sva (
    input logic       clk,
    input logic       reset,
    input logic [3:0] load,
    input logic [3:0] IN,
    input logic [1:0] SHIFT,
    input logic       MODE,
    input logic [3:0] q
);

    // MODE=0 applies a right shift before the final left shift.
    check_mode0_composed_shift: assert property (
        @(posedge clk) disable iff (reset)
        (MODE == 1'b0) |-> (q == ((IN >> SHIFT) << SHIFT))
    );

    // MODE=1 applies a left shift before the final left shift.
    check_mode1_composed_shift: assert property (
        @(posedge clk) disable iff (reset)
        (MODE == 1'b1) |-> (q == ((IN << SHIFT) << SHIFT))
    );

    // With MODE=0 and SHIFT=0, q passes IN through.
    check_mode0_shift0_passthrough: assert property (
        @(posedge clk) disable iff (reset)
        (MODE == 1'b0 && SHIFT == 2'd0) |-> (q == IN)
    );

    // With MODE=0 and SHIFT=1, only the LSB is cleared.
    check_mode0_shift1_result: assert property (
        @(posedge clk) disable iff (reset)
        (MODE == 1'b0 && SHIFT == 2'd1) |-> (q == {IN[3:1], 1'b0})
    );

    // With MODE=0 and SHIFT=2, only IN[3:2] remain.
    check_mode0_shift2_result: assert property (
        @(posedge clk) disable iff (reset)
        (MODE == 1'b0 && SHIFT == 2'd2) |-> (q == {IN[3:2], 2'b00})
    );

    // With MODE=0 and SHIFT=3, only IN[3] remains.
    check_mode0_shift3_result: assert property (
        @(posedge clk) disable iff (reset)
        (MODE == 1'b0 && SHIFT == 2'd3) |-> (q == {IN[3], 3'b000})
    );

    // With MODE=1 and SHIFT=0, q passes IN through.
    check_mode1_shift0_passthrough: assert property (
        @(posedge clk) disable iff (reset)
        (MODE == 1'b1 && SHIFT == 2'd0) |-> (q == IN)
    );

    // With MODE=1 and SHIFT=1, only IN[1:0] remain.
    check_mode1_shift1_result: assert property (
        @(posedge clk) disable iff (reset)
        (MODE == 1'b1 && SHIFT == 2'd1) |-> (q == {IN[1:0], 2'b00})
    );

    // With MODE=1 and SHIFT=2, the 4-bit result becomes zero.
    check_mode1_shift2_result: assert property (
        @(posedge clk) disable iff (reset)
        (MODE == 1'b1 && SHIFT == 2'd2) |-> (q == 4'b0000)
    );

    // With MODE=1 and SHIFT=3, the 4-bit result becomes zero.
    check_mode1_shift3_result: assert property (
        @(posedge clk) disable iff (reset)
        (MODE == 1'b1 && SHIFT == 2'd3) |-> (q == 4'b0000)
    );

endmodule