module d_flip_flop_sva (
    input logic clk,
    input logic d,
    input logic q
);
    // If d is 1 at a rising edge, q is 1 at the next rising edge.
    check_q_next_is_one_when_d_one: assert property (
        @(posedge clk) (d == 1'b1) |=> (q == 1'b1)
    );

    // If d is 0 at a rising edge, q is 0 at the next rising edge.
    check_q_next_is_zero_when_d_zero: assert property (
        @(posedge clk) (d == 1'b0) |=> (q == 1'b0)
    );
endmodule