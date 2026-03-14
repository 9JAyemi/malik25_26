module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] d,
    input logic [7:0] in,
    input logic [7:0] q,
    input logic [7:0] rising_edge,
    input logic [7:0] sum_output
);
    // Track past-valid to safely use $past after first cycle.
    logic past_valid;
    always @(posedge clk) begin
        if (reset) past_valid <= 1'b0;
        else past_valid <= 1'b1;
    end

    ///// Top-level wiring/combinational mapping /////
    // rising_edge must equal sum_output (direct assign).
    check_rising_edge_equals_sum_output: assert property (
        @(posedge clk) disable iff (reset) rising_edge == sum_output
    );
    // sum_output equals q + d (adder with q wired from rising_edge_detection output).
    check_sum_output_equals_q_plus_d: assert property (
        @(posedge clk) disable iff (reset) sum_output == (q + d)
    );
    // rising_edge equals q + d (by wiring through sum_output).
    check_rising_edge_equals_q_plus_d: assert property (
        @(posedge clk) disable iff (reset) rising_edge == (q + d)
    );
    // (sum_output - d) recovers q (modulo-256).
    check_sum_minus_d_equals_q: assert property (
        @(posedge clk) disable iff (reset) (sum_output - d) == q
    );
    // (sum_output - q) recovers d (modulo-256).
    check_sum_minus_q_equals_d: assert property (
        @(posedge clk) disable iff (reset) (sum_output - q) == d
    );
    // If q and d are stable, sum_output must be stable.
    check_sum_stable_when_q_and_d_stable: assert property (
        @(posedge clk) disable iff (reset) past_valid && $stable(q) && $stable(d) |-> $stable(sum_output)
    );
    // If q and d are stable, rising_edge must be stable.
    check_rising_stable_when_q_and_d_stable: assert property (
        @(posedge clk) disable iff (reset) past_valid && $stable(q) && $stable(d) |-> $stable(rising_edge)
    );

    ///// Rising-edge detector sequential behavior on q /////
    // Exact next-state equation: q == $past(q) & ~($past(in) ^ $past(q)).
    check_q_exact_update: assert property (
        @(posedge clk) disable iff (reset) past_valid |-> (q == ($past(q) & ~($past(in) ^ $past(q))))
    );
    // q cannot gain new 1-bits relative to previous q.
    check_q_no_new_ones: assert property (
        @(posedge clk) disable iff (reset) past_valid |-> ((q & ~($past(q))) == 8'h00)
    );
    // Bits where $past(in) != $past(q) must clear to 0 in q.
    check_q_zero_on_mismatch_bits: assert property (
        @(posedge clk) disable iff (reset) past_valid |-> ((q & ($past(in) ^ $past(q))) == 8'h00)
    );
    // Bits where $past(in) == $past(q) must hold their previous q value.
    check_q_hold_on_match_bits: assert property (
        @(posedge clk) disable iff (reset) past_valid |-> (((q ^ $past(q)) & ~($past(in) ^ $past(q))) == 8'h00)
    );
endmodule