module dff_or_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] d,
    input logic [7:0] e,
    input logic [7:0] q
);
    // During reset, q must equal 8'h80 OR e (as q_reg resets to 8'h80).
    check_reset_or_value: assert property (
        @(posedge clk) reset |-> (q == (8'h80 | e))
    );

    // On the cycle reset deasserts, q still reflects 8'h80 OR e before capturing d.
    check_reset_release_cycle: assert property (
        @(posedge clk) $fell(reset) |-> (q == (8'h80 | e))
    );

    // e bits force corresponding q bits HIGH due to OR.
    check_e_forces_ones: assert property (
        @(posedge clk) (q & e) == e
    );

    // When not in reset across cycles, q equals (previous d) OR current e.
    check_q_equals_past_d_or_e: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (q == ($past(d) | e))
    );

    // With e == 0 and not in reset across cycles, q equals previous d.
    check_e_zero_uses_past_d: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && (e == 8'h00)) |-> (q == $past(d))
    );

    // With e == 0xFF, q must be 0xFF regardless of d or reset state.
    check_e_all_ones_saturates_q: assert property (
        @(posedge clk) (e == 8'hFF) |-> (q == 8'hFF)
    );

    // When not in reset across cycles, q bits not masked by e follow previous d.
    check_masked_bits_follow_past_d: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> ((q & ~e) == ($past(d) & ~e))
    );

    // When not in reset across cycles, q == 0 implies both e == 0 and previous d == 0.
    check_q_zero_implies_e_and_past_d_zero: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && (q == 8'h00)) |-> ((e == 8'h00) && ($past(d) == 8'h00))
    );

    // When not in reset across cycles and previous d == 0xFF, q must be 0xFF.
    check_past_d_all_ones_saturates_q: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && ($past(d) == 8'hFF)) |-> (q == 8'hFF)
    );

    // When not in reset across cycles, previous d == 0 and e == 0 implies q == 0.
    check_past_d_zero_and_e_zero_imply_q_zero: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset) && ($past(d) == 8'h00) && (e == 8'h00)) |-> (q == 8'h00)
    );
endmodule