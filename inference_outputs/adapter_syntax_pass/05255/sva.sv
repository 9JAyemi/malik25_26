module binary_multiplier_sva (
    input logic clk,
    input logic reset,
    input logic [15:0] a,
    input logic [15:0] b,
    input logic [31:0] result
);

    // Reset clears the registered result on the next clock.
    check_reset_clears_result: assert property (
        @(posedge clk) reset |=> (result == 32'd0)
    );

    // Outside reset, result holds its previous value.
    check_result_holds_without_reset: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (result == $past(result))
    );

endmodule