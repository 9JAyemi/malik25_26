module top_module_sva (
    input logic clk,
    input logic reset,
    input logic signed [3:0] A,
    input logic signed [3:0] B,
    input logic select,
    input logic signed [3:0] out
);

    // Reset forces the registered output to zero.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |-> (out == 4'sd0)
    );

    // When select is low, out captures the 4-bit signed sum on the next cycle.
    check_add_path_updates_out: assert property (
        @(posedge clk) disable iff (reset)
        (!select) |=> (out == ($past(A) + $past(B)))
    );

    // When select is high and A is zero, out captures the zero-status encoding.
    check_select_zero_encoding: assert property (
        @(posedge clk) disable iff (reset)
        (select && (A == 4'sd0)) |=> (out == 4'b0100)
    );

    // When select is high and A is negative, out captures the negative-status encoding.
    check_select_negative_encoding: assert property (
        @(posedge clk) disable iff (reset)
        (select && (A < 4'sd0)) |=> (out == 4'b0010)
    );

    // When select is high and A is positive, out captures the positive-status encoding.
    check_select_positive_encoding: assert property (
        @(posedge clk) disable iff (reset)
        (select && (A > 4'sd0)) |=> (out == 4'b0001)
    );

endmodule