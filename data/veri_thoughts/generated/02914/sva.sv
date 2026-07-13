module top_module_sva (
    input logic clk,
    input logic reset,        // Synchronous active-high reset
    input logic [7:0] in,     // Only in[0] is used functionally
    input logic out
);
    // Clock: clk. Reset: reset (sync active-high).
    // Logic: mixed (3-bit shift reg + combinational NAND/NOR).
    // Behavior: out = shift_out[2] & ~(shift_out[0] & shift_out[1]); shift_out = {prev[1:0], in[0]} on clk; reset->shift_out=0.

    ///// Reset behavior /////
    // While reset is asserted, out must be 0.
    reset_forces_out_low: assert property (
        @(posedge clk) reset |-> (out == 1'b0)
    );

    // One cycle after any reset cycle, out is 0.
    post_reset_out_low_1: assert property (
        @(posedge clk) disable iff (reset)
            $past(reset) |-> (out == 1'b0)
    );

    // Two cycles after any reset cycle, out is 0.
    post_reset_out_low_2: assert property (
        @(posedge clk) disable iff (reset)
            $past(reset,2) |-> (out == 1'b0)
    );

    ///// Functional relation to in[0] history (no reset in last 2 cycles) /////
    // When no reset in the last 2 cycles, exact Boolean relation to in[0] history holds.
    out_matches_history: assert property (
        @(posedge clk) disable iff (reset)
            ($past(reset,1) == 1'b0 && $past(reset,2) == 1'b0) |-> 
                (out == ($past(in[0],2) & ~(in[0] & $past(in[0],1))))
    );

    // If in[0] two cycles ago was 0 (and no recent reset), out is 0.
    i2_zero_implies_out_zero: assert property (
        @(posedge clk) disable iff (reset)
            ($past(reset,1) == 1'b0 && $past(reset,2) == 1'b0 && ($past(in[0],2) == 1'b0)) |-> 
                (out == 1'b0)
    );

    // Two consecutive 1s on in[0] (prev and curr) always force out low.
    two_ones_in_a_row_force_low: assert property (
        @(posedge clk) disable iff (reset)
            (in[0] && $past(in[0])) |-> (out == 1'b0)
    );

    // If i2==1 and not both curr/prev are 1 (no recent reset), out is 1.
    i2_one_and_not_both_ones_implies_out_one: assert property (
        @(posedge clk) disable iff (reset)
            ($past(reset,1) == 1'b0 && $past(reset,2) == 1'b0 &&
             $past(in[0],2) == 1'b1 && !(in[0] && $past(in[0],1))) |-> 
                (out == 1'b1)
    );

    // If out is 1 (no recent reset), then i2 must be 1.
    out_one_requires_i2_one: assert property (
        @(posedge clk) disable iff (reset)
            ($past(reset,1) == 1'b0 && $past(reset,2) == 1'b0 && out == 1'b1) |-> 
                ($past(in[0],2) == 1'b1)
    );

    // If out is 1 (no recent reset), curr and prev in[0] cannot both be 1.
    out_one_requires_not_both_curr_prev_one: assert property (
        @(posedge clk) disable iff (reset)
            ($past(reset,1) == 1'b0 && $past(reset,2) == 1'b0 && out == 1'b1) |-> 
                !(in[0] && $past(in[0],1))
    );

    // If curr in[0]==0 (no recent reset), out equals i2.
    curr_zero_makes_out_equal_i2: assert property (
        @(posedge clk) disable iff (reset)
            ($past(reset,1) == 1'b0 && $past(reset,2) == 1'b0 && in[0] == 1'b0) |-> 
                (out == $past(in[0],2))
    );

    // If prev in[0]==0 (no recent reset), out equals i2.
    prev_zero_makes_out_equal_i2: assert property (
        @(posedge clk) disable iff (reset)
            ($past(reset,1) == 1'b0 && $past(reset,2) == 1'b0 && $past(in[0],1) == 1'b0) |-> 
                (out == $past(in[0],2))
    );

endmodule