module carry_lookahead_multiplier_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic clk,
    input logic reset,
    input logic [15:0] result
);

    // A reset cycle clears the registered result by the following clock.
    check_reset_clears_result: assert property (
        @(posedge clk) reset |=> (result == 16'h0000)
    );

    // Outside reset, result follows the registered RTL sum expression.
    check_result_implements_rtl_sum: assert property (
        @(posedge clk) disable iff (reset)
        !reset |=> (result == ({8'b0, $past(a)} + ({8'b0, $past(b)} << 8)))
    );

    // Outside reset, the low byte of result captures a.
    check_result_low_byte_captures_a: assert property (
        @(posedge clk) disable iff (reset)
        !reset |=> (result[7:0] == $past(a))
    );

    // Outside reset, the high byte of result captures b.
    check_result_high_byte_captures_b: assert property (
        @(posedge clk) disable iff (reset)
        !reset |=> (result[15:8] == $past(b))
    );

    // Zero inputs produce a zero result on the following non-reset cycle.
    check_zero_inputs_yield_zero_result: assert property (
        @(posedge clk) disable iff (reset)
        ((a == 8'h00) && (b == 8'h00)) |=> (result == 16'h0000)
    );

    // A zero a input clears the low byte on the following non-reset cycle.
    check_zero_a_clears_low_byte: assert property (
        @(posedge clk) disable iff (reset)
        (a == 8'h00) |=> (result[7:0] == 8'h00)
    );

    // A zero b input clears the high byte on the following non-reset cycle.
    check_zero_b_clears_high_byte: assert property (
        @(posedge clk) disable iff (reset)
        (b == 8'h00) |=> (result[15:8] == 8'h00)
    );

endmodule