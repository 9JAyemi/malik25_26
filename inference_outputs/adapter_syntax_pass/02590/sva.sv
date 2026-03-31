module d_flip_flop_mux_sva (
    input logic clk,
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic sel,
    input logic [7:0] q
);

    // q reflects the d1 data sampled on the previous falling edge.
    check_q_captures_d1: assert property (
        @(negedge clk) 1'b1 |=> (q == $past(d1))
    );

    // q reflects the d2 data sampled on the previous falling edge.
    check_q_captures_d2: assert property (
        @(negedge clk) 1'b1 |=> (q == $past(d2))
    );

    // q always matches the d1 data sampled on the previous falling edge.
    check_q_matches_past_d1: assert property (
        @(negedge clk) 1'b1 |=> (q == $past(d1))
    );

    // q always matches the d2 data sampled on the previous falling edge.
    check_q_matches_past_d2: assert property (
        @(negedge clk) 1'b1 |=> (q == $past(d2))
    );

endmodule