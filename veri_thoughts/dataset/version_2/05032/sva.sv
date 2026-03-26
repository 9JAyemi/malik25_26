module dff_16_sva (
    input logic clk,
    input logic reset,
    input logic [15:0] d,
    input logic [15:0] q
);

    // Reset forces q low on the next sampled cycle.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |=> (q == 16'h0000)
    );

    // When reset is low, q captures d from the previous rising edge.
    check_q_captures_d: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |=> (q == $past(d))
    );

endmodule