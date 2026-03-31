module top_module_sva (
    input logic clk,
    input logic reset,      // Synchronous active-high reset
    input logic [7:0] d1,   // 8-bit input for adder 1
    input logic [7:0] d2,   // 8-bit input for adder 2
    input logic select,     // Select input to choose between adder 1 and adder 2
    input logic [7:0] q,    // 8-bit output from the functional module
    input logic [7:0] q1,   // Internal state of q1
    input logic [7:0] q2,   // Internal state of q2
    input logic cin1,       // Internal state of cin1
    input logic cin2,       // Internal state of cin2
    input logic [7:0] sum1, // Internal sum from adder 1
    input logic [7:0] sum2, // Internal sum from adder 2
    input logic cout1,      // Internal cout from adder 1
    input logic cout2       // Internal cout from adder 2
);
    ///// Reset behavior /////
    // On reset, q, q1, q2, cin1, cin2 are driven to 0 on the next cycle.
    reset_clears_regs: assert property (
        @(posedge clk) reset |=> (q == 8'h00) && (q1 == 8'h00) && (q2 == 8'h00) && (cin1 == 1'b0) && (cin2 == 1'b0)
    );

    ///// Combinational adder behavior /////
    // sum1 equals a + b + cin1.
    adder1_sum_definition: assert property (
        @(posedge clk) disable iff (reset) sum1 == (d1 + q1 + cin1)
    );
    // sum2 equals a + b + cin2.
    adder2_sum_definition: assert property (
        @(posedge clk) disable iff (reset) sum2 == (d2 + q2 + cin2)
    );
    // cout1 equals carry-out of a + b + cin1.
    adder1_cout_definition: assert property (
        @(posedge clk) disable iff (reset) cout1 == (({1'b0, d1} + {1'b0, q1} + {1'b0, cin1})[8])
    );
    // cout2 equals carry-out of a + b + cin2.
    adder2_cout_definition: assert property (
        @(posedge clk) disable iff (reset) cout2 == (({1'b0, d2} + {1'b0, q2} + {1'b0, cin2})[8])
    );

    ///// Sequential update rules /////
    // When select=1, q updates to sum1 on the next cycle.
    q_updates_on_select1: assert property (
        @(posedge clk) disable iff (reset) select |=> (q == $past(sum1))
    );
    // When select=0, q updates to sum2 on the next cycle.
    q_updates_on_select0: assert property (
        @(posedge clk) disable iff (reset) !select |=> (q == $past(sum2))
    );
    // When select=1, q1 captures d1 on the next cycle.
    q1_captures_d1_on_select1: assert property (
        @(posedge clk) disable iff (reset) select |=> (q1 == $past(d1))
    );
    // When select=1, cin1 is cleared on the next cycle.
    cin1_clears_on_select1: assert property (
        @(posedge clk) disable iff (reset) select |=> (cin1 == 1'b0)
    );
    // When select=1, q2 captures sum1 on the next cycle.
    q2_captures_sum1_on_select1: assert property (
        @(posedge clk) disable iff (reset) select |=> (q2 == $past(sum1))
    );
    // When select=1, cin2 captures cout1 on the next cycle.
    cin2_captures_cout1_on_select1: assert property (
        @(posedge clk) disable iff (reset) select |=> (cin2 == $past(cout1))
    );
    // When select=0, q2 captures d2 on the next cycle.
    q2_captures_d2_on_select0: assert property (
        @(posedge clk) disable iff (reset) !select |=> (q2 == $past(d2))
    );
    // When select=0, cin2 is cleared on the next cycle.
    cin2_clears_on_select0: assert property (
        @(posedge clk) disable iff (reset) !select |=> (cin2 == 1'b0)
    );
    // When select=0, q1 captures sum2 on the next cycle.
    q1_captures_sum2_on_select0: assert property (
        @(posedge clk) disable iff (reset) !select |=> (q1 == $past(sum2))
    );
    // When select=0, cin1 captures cout2 on the next cycle.
    cin1_captures_cout2_on_select0: assert property (
        @(posedge clk) disable iff (reset) !select |=> (cin1 == $past(cout2))
    );
endmodule