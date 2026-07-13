module top_module_sva (
    input logic clk,
    input logic reset,      // synchronous active-high reset
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic select,
    input logic [7:0] q,
    input logic [7:0] q1,
    input logic [7:0] q2,
    input logic cin1,
    input logic cin2,
    input logic [7:0] sum1,
    input logic [7:0] sum2,
    input logic cout1,
    input logic cout2
);

// Reset clears q, q1, q2, cin1, cin2, sum1, sum2, and couts.
    check_reset_clears_all: assert property (
        @(posedge clk) reset |=> (q == 8'h00) && (q1 == 8'h00) && (q2 == 8'h00) &&
                                 (cin1 == 1'b0) && (cin2 == 1'b0) &&
                                 (sum1 == 8'h00) && (sum2 == 8'h00) &&
                                 (cout1 == 1'b0) && (cout2 == 1'b0)
    );

// With select high, q captures sum1 on the next cycle.
    check_q_captures_sum1_when_select_high: assert property (
        @(posedge clk) disable iff (reset)
        select |=> (q == $past(sum1))
    );

// With select low, q captures sum2 on the next cycle.
    check_q_captures_sum2_when_select_low: assert property (
        @(posedge clk) disable iff (reset)
        !select |=> (q == $past(sum2))
    );

// With select high, q1 captures d1 and cin1=0 on the next cycle.
    check_q1_captures_d1_when_select_high: assert property (
        @(posedge clk) disable iff (reset)
        select |=> (q1 == $past(d1)) && (cin1 == 1'b0)
    );

// With select high, q2 captures sum1 and cin2=cout1 on the next cycle.
    check_q2_captures_sum1_when_select_high: assert property (
        @(posedge clk) disable iff (reset)
        select |=> (q2 == $past(sum1)) && (cin2 == $past(cout1))
    );

// With select low, q2 captures d2 and cin2=0 on the next cycle.
    check_q2_captures_d2_when_select_low: assert property (
        @(posedge clk) disable iff (reset)
        !select |=> (q2 == $past(d2)) && (cin2 == 1'b0)
    );

// With select low, q1 captures sum2 and cin1=cout2 on the next cycle.
    check_q1_captures_sum2_when_select_low: assert property (
        @(posedge clk) disable iff (reset)
        !select |=> (q1 == $past(sum2)) && (cin1 == $past(cout2))
    );

// sum1 is the 8-bit addition of d1 and q1 with cin1.
    check_sum1_addition: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |-> ({cout1, sum1} == ({1'b0, d1} + {1'b0, q1} + {1'b0, cin1}))
    );

// sum2 is the 8-bit addition of d2 and q2 with cin2.
    check_sum2_addition: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |-> ({cout2, sum2} == ({1'b0, d2} + {1'b0, q2} + {1'b0, cin2}))
    );

endmodule
