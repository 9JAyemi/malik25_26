module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] d,
    input logic [7:0] q
);
    // Clocks/resets: clk is posedge; reset is active-HIGH synchronous.
    // Mixed logic: sequential (binary_counter, flip_flop) + combinational (mux, assigns).
    // Behavior: q = (counter_out[3]) ? q_ff : {4'b0000, counter_out}; during reset counter_out=0 so q=8'h00.

    ///// Reset behavior /////
    // While reset is asserted, q must be 0x00.
    reset_q_zero: assert property (
        @(posedge clk) reset |-> (q == 8'h00)
    );

    // If reset stays asserted across consecutive cycles, q remains 0 and stable.
    reset_hold_q_zero_stable: assert property (
        @(posedge clk) reset && $past(reset) |-> (q == 8'h00) && (q == $past(q))
    );

    // First cycle after a reset cycle, the upper nibble of q is zero.
    upper_zero_after_reset_fall: assert property (
        @(posedge clk) disable iff (reset) $past(reset) |-> (q[7:4] == 4'b0000)
    );

    ///// Upper-nibble invariants /////
    // Once the upper nibble is zero, it remains zero on the next cycle.
    upper_zero_sticky_one_step: assert property (
        @(posedge clk) disable iff (reset) (q[7:4] == 4'b0000) |=> (q[7:4] == 4'b0000)
    );

    // The upper nibble becomes zero at least once within any 9-cycle window (0..8).
    upper_zero_within_8: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |-> ##[0:8] (q[7:4] == 4'b0000)
    );

    // q becomes exactly 0x00 at least once within any 17-cycle window (0..16).
    q_zero_within_16: assert property (
        @(posedge clk) disable iff (reset) 1'b1 |-> ##[0:16] (q == 8'h00)
    );

    // If upper nibble is non-zero and reset stays low across the boundary, q holds its value next cycle.
    upper_nonzero_holds_one_cycle: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && (q[7:4] != 4'b0000)) |-> ##1 (reset || (q == $past(q)))
    );

    // If upper nibble is non-zero and reset stays low, the upper nibble stays non-zero next cycle.
    upper_nonzero_stays_nonzero_one_cycle: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && (q[7:4] != 4'b0000)) |-> ##1 (!reset && (q[7:4] != 4'b0000))
    );
endmodule