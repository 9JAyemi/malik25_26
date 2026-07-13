module top_module_sva (
    input logic clk,
    input logic [7:0] d,
    input logic [7:0] q
);

// q captures d on the previous negedge of clk.
    check_q_captures_d_on_prev_negedge: assert property (
        @(posedge clk) 1'b1 |=> (q == $past(d))
    );

// q reflects the d value present on the previous negedge of clk.
    check_q_matches_prev_d: assert property (
        @(negedge clk) 1'b1 |=> (q == $past(d))
    );

endmodule
