module top_module_sva (
    input logic clk,
    input logic reset,        // Active-low asynchronous in RTL (negedge sensitive), asserted low
    input logic [2:0] D,
    input logic S,            // Unused in RTL
    input logic P,
    input logic [7:0] C,
    input logic [7:0] q,
    input logic [3:0] bcd_out,
    input logic [7:0] c_out
);
    ///// Binary-to-BCD converter checks /////
    // bcd_out must be zero-extended D.
    check_bcd_zero_extend: assert property (
        @(posedge clk) disable iff (!reset) bcd_out == {1'b0, D}
    );
    // bcd_out MSB is always 0 (range 0..7).
    check_bcd_msb_zero: assert property (
        @(posedge clk) disable iff (!reset) bcd_out[3] == 1'b0
    );

    ///// Priority multiplexer checks /////
    // When P is 1, c_out equals C.
    check_mux_priority_high_routes_C: assert property (
        @(posedge clk) disable iff (!reset) P |-> (c_out == C)
    );
    // When P is 0, c_out equals zero-extended bcd_out.
    check_mux_priority_low_routes_bcd: assert property (
        @(posedge clk) disable iff (!reset) !P |-> (c_out == {4'b0000, bcd_out})
    );
    // When P is 0, upper nibble of c_out is 0.
    check_mux_priority_low_upper_zero: assert property (
        @(posedge clk) disable iff (!reset) !P |-> (c_out[7:4] == 4'b0000)
    );
    // When P is 0, lower nibble of c_out equals bcd_out.
    check_mux_priority_low_lower_matches_bcd: assert property (
        @(posedge clk) disable iff (!reset) !P |-> (c_out[3:0] == bcd_out)
    );

    ///// BCD adder (sequential) checks /////
    // While reset is asserted low at clock edge, q is 0.
    check_reset_clears_q: assert property (
        @(posedge clk) (!reset) |-> (q == 8'h00)
    );
    // With reset high in consecutive cycles, q updates to previous-cycle sum.
    check_q_updates_with_sum: assert property (
        @(posedge clk) disable iff (!reset) $past(reset) |-> (q == $past(bcd_out + c_out))
    );
    // If previous cycle had P=1 (and reset high), q equals previous C + bcd_out.
    check_q_update_when_prev_priority_high: assert property (
        @(posedge clk) disable iff (!reset) ($past(reset) && $past(P)) |-> (q == $past(C + bcd_out))
    );
    // If previous cycle had P=0 (and reset high), q equals previous zero-extended bcd_out + bcd_out.
    check_q_update_when_prev_priority_low: assert property (
        @(posedge clk) disable iff (!reset) ($past(reset) && !$past(P)) |-> (q == $past({4'b0000, bcd_out} + bcd_out))
    );
endmodule