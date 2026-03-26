module dff_keep_34_sva (
    input logic        clk,
    input logic        rst,
    input logic [33:0] d,
    input logic [33:0] q
);

    // q is zero whenever reset is sampled high.
    check_reset_clears_q: assert property (
        @(posedge clk) rst |-> (q == 34'b0)
    );

    // q stays zero on the first clock after reset is released.
    check_q_zero_on_reset_release: assert property (
        @(posedge clk) disable iff (rst) $fell(rst) |-> (q == 34'b0)
    );

    // Outside reset, q captures d from the previous clock edge.
    check_q_captures_d: assert property (
        @(posedge clk) disable iff (rst) 1'b1 |=> (q == $past(d))
    );

endmodule