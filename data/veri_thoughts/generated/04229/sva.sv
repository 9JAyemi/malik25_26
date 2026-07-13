module binary_counter_sva (
    input logic       clk,
    input logic       rst,
    input logic [3:0] q
);

    // A sampled low reset forces q to zero by the next sampled clock edge.
    check_reset_clears_by_next_clk: assert property (
        @(posedge clk) !rst |=> (q == 4'b0000)
    );

    // Outside reset, q is either zero or the previous sampled value plus one.
    check_q_advances_or_is_zero: assert property (
        @(posedge clk) disable iff (!rst)
        1'b1 |=> ((q == 4'b0000) || (q == ($past(q) + 4'd1)))
    );

    // When q leaves zero on an active cycle, the next nonzero value is one.
    check_zero_to_one_transition: assert property (
        @(posedge clk) disable iff (!rst)
        1'b1 |=> ((!($past(q) == 4'b0000 && q != 4'b0000)) || (q == 4'b0001))
    );

    // A sampled value of 4'hF wraps to zero on the next active sampled cycle.
    check_wrap_from_f_to_zero: assert property (
        @(posedge clk) disable iff (!rst)
        1'b1 |=> (($past(q) != 4'hF) || (q == 4'h0))
    );

endmodule