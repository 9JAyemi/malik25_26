module multiplier_sva(
    input logic signed [7:0] a,
    input logic signed [7:0] b,
    input logic sel,
    input logic reset,
    input logic clk,
    input logic signed [15:0] out
);

    // Reset clears both state registers, so out is zero on the following cycle.
    check_reset_clears_out: assert property (
        @(posedge clk) reset |=> (out == 16'sd0)
    );

    // With sum selected in two active cycles, out shows the prior cycle's addition.
    check_sum_path_latency: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset) && $past(sel) && sel)
        |-> (out == ($past(a) + $past(b)))
    );

    // With product selected in two active cycles, out shows the prior cycle's multiplication.
    check_product_path_latency: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset) && !$past(sel) && !sel)
        |-> (out == ($past(a) * $past(b)))
    );

    // With stable inputs on the sum path, out matches the current visible addition.
    check_sum_path_stable_inputs: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset) && $past(sel) && sel &&
         (a == $past(a)) && (b == $past(b)))
        |-> (out == (a + b))
    );

    // With stable inputs on the product path, out matches the current visible multiplication.
    check_product_path_stable_inputs: assert property (
        @(posedge clk) disable iff (reset)
        (!$initstate && $past(!reset) && !$past(sel) && !sel &&
         (a == $past(a)) && (b == $past(b)))
        |-> (out == (a * b))
    );

endmodule