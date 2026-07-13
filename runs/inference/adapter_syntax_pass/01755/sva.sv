module top_module_sva (
    input logic clk,
    input logic reset,      // Synchronous active-high reset
    input logic [7:0] d1,   // 8-bit input for adder 1
    input logic [7:0] d2,   // 8-bit input for adder 2
    input logic select,     // Select input to choose between adder 1 and adder 2
    input logic [7:0] q,    // 8-bit output from the functional module
    input logic [7:0] q1,
    input logic [7:0] q2,
    input logic cin1,
    input logic cin2,
    input logic [7:0] sum1,
    input logic [7:0] sum2,
    input logic cout1,
    input logic cout2
);

    ///// Reset behavior /////
    // On reset, q must be 0 on the next cycle.
    reset_clears_q_next: assert property (
        @(posedge clk) reset |=> (q == 8'h00)
    );

    // On reset, q1 must be 0 on the next cycle.
    reset_clears_q1_next: assert property (
        @(posedge clk) reset |=> (q1 == 8'h00)
    );

    // On reset, q2 must be 0 on the next cycle.
    reset_clears_q2_next: assert property (
        @(posedge clk) reset |=> (q2 == 8'h00)
    );

    // On reset, cin1 must be 0 on the next cycle.
    reset_clears_cin1_next: assert property (
        @(posedge clk) reset |=> (cin1 == 1'b0)
    );

    // On reset, cin2 must be 0 on the next cycle.
    reset_clears_cin2_next: assert property (
        @(posedge clk) reset |=> (cin2 == 1'b0)
    );

    // On reset, q1 must equal d1 on the next cycle.
    reset_loads_d1_into_q1_next: assert property (
        @(posedge clk) reset |=> (q1 == $past(d1))
    );

    // On reset, q2 must equal d2 on the next cycle.
    reset_loads_d2_into_q2_next: assert property (
        @(posedge clk) reset |=> (q2 == $past(d2))
    );

    // On reset, sum1 must equal d1 + q1 + cin1 on the next cycle.
    reset_sum1_next: assert property (
        @(posedge clk) reset |=> (sum1 == ($past(d1) + $past(q1) + $past(cin1)))
    );

    // On reset, sum2 must equal d2 + q2 + cin2 on the next cycle.
    reset_sum2_next: assert property (
        @(posedge clk) reset |=> (sum2 == ($past(d2) + $past(q2) + $past(cin2)))
    );

    // On reset, cout1 must equal carry-out of d1 + q1 + cin1 on the next cycle.
    reset_cout1_next: assert property (
        @(posedge clk) reset |=> (cout1 == (({1'b0, $past(d1)} + {1'b0, $past(q1)} + $past(cin1)) >= 9'h100))
    );

    // On reset, cout2 must equal carry-out of d2 + q2 + cin2 on the next cycle.
    reset_cout2_next: assert property (
        @(posedge clk) reset |=> (cout2 == (({1'b0, $past(d2)} + {1'b0, $past(q2)} + $past(cin2)) >= 9'h100))
    );

    // On reset, q must equal sum1 on the next cycle.
    reset_q_follows_sum1_next: assert property (
        @(posedge clk) reset |=> (q == $past(sum1))
    );

    // On reset, q must equal sum2 on the next cycle.
    reset_q_follows_sum2_next: assert property (
        @(posedge clk) reset |=> (q == $past(sum2))
    );

    // On reset, q1 must equal d1 on the next cycle.
    reset_q1_follows_d1_next: assert property (
        @(posedge clk) reset |=> (q1 == $past(d1))
    );

    // On reset, q2 must equal d2 on the next cycle.
    reset_q2_follows_d2_next: assert property (
        @(posedge clk) reset |=> (q2 == $past(d2))
    );

    // On reset, cin1 must be 0 on the next cycle.
    reset_cin1_zero_next: assert property (
        @(posedge clk) reset |=> (cin1 == 1'b0)
    );

    // On reset, cin2 must be 0 on the next cycle.
    reset_cin2_zero_next: assert property (
        @(posedge clk) reset |=> (cin2 == 1'b0)
    );

    // On reset, cout1 must be 0 on the next cycle.
    reset_cout1_zero_next: assert property (
        @(posedge clk) reset |=> (cout1 == 1'b0)
    );

    // On reset, cout2 must be 0 on the next cycle.
    reset_cout2_zero_next: assert property (
        @(posedge clk) reset |=> (cout2 == 1'b0)
    );

    // On reset, sum1 must equal d1 + q1 + cin1 on the next cycle.
    reset_sum1_next: assert property (
        @(posedge clk) reset |=> (sum1 == ($past(d1) + $past(q1) + $past(cin1)))
    );

    // On reset, sum2 must equal d2 + q2 + cin2 on the next cycle.
    reset_sum2_next: assert property (
        @(posedge clk) reset |=> (sum2 == ($past(d2) + $past(q2) + $past(cin2)))
    );

    // On reset, q must equal sum1 on the next cycle.
    reset_q_follows_sum1_next: assert property (
        @(posedge clk) reset |=> (q == $past(sum1))
    );

    // On reset, q must equal sum2 on the next cycle.
    reset_q_follows_sum2_next: assert property (
        @(posedge clk) reset |=> (q == $past(sum2))
    );

    // On reset, q1 must equal d1 on the next cycle.
    reset_q1_follows_d1_next: assert property (
        @(posedge clk) reset |=> (q1 == $past(d1))
    );

    // On reset, q2 must equal d2 on the next cycle.
    reset_q2_follows_d2_next: assert property (
        @(posedge clk) reset |=> (q2 == $past(d2))
    );

    // On reset, cin1 must be 0 on the next cycle.
    reset_cin1_zero_next: assert property (
        @(posedge clk) reset |=> (cin1 == 1'b0)
    );

    // On reset, cin2 must be 0 on the next cycle.
    reset_cin2_zero_next: assert property (
        @(posedge clk) reset |=> (cin2 == 1'b0)
    );

    // On reset, cout1 must be 0 on the next cycle.
    reset_cout1_zero_next: assert property (
        @(posedge clk) reset |=> (cout1 == 1'b0)
    );

    // On reset, cout2 must be 0 on the next cycle.
    reset_cout2_zero_next: assert property (
        @(posedge clk) reset |=> (cout2 == 1'b0)
    );

    // On reset, q must equal sum1 on the next cycle.
    reset_q_follows_sum1_next: assert property (
        @(posedge clk) reset |=> (q == $past(sum1))
    );

    // On reset, q must equal sum2 on the next cycle.
    reset_q_follows_sum2_next: assert property (
        @(posedge clk) reset |=> (q == $past(sum2))
    );

    // On reset, q1 must equal d1 on the next cycle.
    reset_q1_follows_d1_next: assert property (
        @(posedge clk) reset |=> (q1 == $past(d1))
    );

    // On reset, q2 must equal d2 on the next cycle.
    reset_q2_follows_d2_next: assert property (
        @(posedge clk) reset |=> (q2 == $past(d2))
    );

    // On reset, cin1 must be 0 on the next cycle.
    reset_cin1_zero_next: assert property (
        @(posedge clk) reset |=> (cin1 == 1'b0)
    );

    // On reset, cin2 must be 0 on the next cycle.
    reset_cin2_zero_next: assert property (
        @(posedge clk) reset |=> (cin2 == 1'b0)
    );

    // On reset, cout1 must be 0 on the next cycle.
    reset_cout1_zero_next: assert property (
        @(posedge clk) reset |=> (cout1 == 1'b0)
    );

    // On reset, cout2 must be 0 on