module clock_gate_sva (
    input logic clk,
    input logic en,
    input logic data,
    input logic gated_clk
);
    // Clock: clk; no reset in RTL. Sequential register of (en && data) with 1-cycle latency to gated_clk.

    // Output equals previous cycle AND of en and data.
    check_gated_clk_matches_prev_and: assert property (
        @(posedge clk) 1'b1 |-> (gated_clk == $past(en && data))
    );

    // If previous cycle en && data was 1, output is 1 now.
    check_gated_clk_high_when_prev_and_high: assert property (
        @(posedge clk) $past(en && data) |-> (gated_clk == 1'b1)
    );

    // If previous cycle en && data was 0, output is 0 now.
    check_gated_clk_low_when_prev_and_low: assert property (
        @(posedge clk) !$past(en && data) |-> (gated_clk == 1'b0)
    );
endmodule