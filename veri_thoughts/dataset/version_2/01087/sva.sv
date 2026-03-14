module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] d,
    input logic select,
    input logic [7:0] q,
    input logic [7:0] reg_out,
    input logic [3:0] counter_out
);
    ///// Register behavior /////
    // On the cycle after reset is asserted, reg_out must be 0x34.
    reg_reset_to_34_next: assert property (
        @(posedge clk) reset |=> (reg_out == 8'h34)
    );
    // While reset remains asserted across cycles, reg_out holds 0x34.
    reg_holds_34_during_reset: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (reg_out == 8'h34)
    );
    // On the cycle reset deasserts, reg_out still reflects the reset value before update.
    reg_deassert_cycle_shows_34: assert property (
        @(posedge clk) ($past(reset) && !reset) |-> (reg_out == 8'h34)
    );
    // When not in reset and previous cycle not in reset, reg_out equals prior d.
    reg_loads_d_from_prev_cycle: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (reg_out == $past(d))
    );

    ///// Counter behavior /////
    // On the cycle after reset is asserted, counter_out must be 0.
    counter_reset_to_0_next: assert property (
        @(posedge clk) reset |=> (counter_out == 4'b0)
    );
    // While reset remains asserted across cycles, counter_out holds 0.
    counter_holds_0_during_reset: assert property (
        @(posedge clk) (reset && $past(reset)) |-> (counter_out == 4'b0)
    );
    // On the cycle reset deasserts, counter_out is 0 before update.
    counter_deassert_cycle_shows_0: assert property (
        @(posedge clk) ($past(reset) && !reset) |-> (counter_out == 4'b0)
    );
    // When not in reset, counter_out increments by 1 modulo 16 each cycle.
    counter_increments_by_1: assert property (
        @(posedge clk) disable iff (reset) counter_out == ($past(counter_out) + 4'd1)
    );
    // When previous value was 15, next value wraps to 0.
    counter_wraps_from_15_to_0: assert property (
        @(posedge clk) disable iff (reset) ($past(counter_out) == 4'hF) |-> (counter_out == 4'h0)
    );

    ///// Adder/output behavior /////
    // q equals reg_out plus zero-extended counter_out (independent of select).
    adder_sum_matches_inputs: assert property (
        @(posedge clk) disable iff (reset) q == (reg_out + {4'b0, counter_out})[7:0]
    );
    // On the cycle after reset is asserted, q must be 0x34 (34 + 0).
    q_after_reset_is_34_next: assert property (
        @(posedge clk) reset |=> (q == 8'h34)
    );
endmodule