module counter_sva (
    input logic clk,
    input logic rst,
    input logic [7:0] value,
    input logic [26:0] ctr_q
);

// Reset clears the counter and value on the next cycle.
    check_reset_clears_state: assert property (
        @(posedge clk) rst |=> (ctr_q == 27'd0 && value == 8'd0)
    );

// The upper 7 bits of ctr_q are reflected into value on the next cycle.
    check_value_captures_upper_bits: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (value == $past(ctr_q[26:19]))
    );

// The least-significant bit of ctr_q is inverted into value on the next cycle.
    check_value_inverts_lsb: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (value[0] == ~$past(ctr_q[0]))
    );

// A 27-bit counter increment wraps from 7F to 00.
    check_counter_wraps_after_max: assert property (
        @(posedge clk) disable iff (rst) (ctr_q == 27'h7FFFFF) |=> (ctr_q == 27'h000000)
    );

// The upper 7 bits of value match the previous cycle's upper 7 bits of ctr_q.
    check_value_upper_bits_stable: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (value[7:1] == $past(ctr_q[26:19]))
    );

// The least-significant bit of value matches the previous cycle's ctr_q LSB.
    check_value_lsb_stable: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (value[0] == ~$past(ctr_q[0]))
    );

endmodule
