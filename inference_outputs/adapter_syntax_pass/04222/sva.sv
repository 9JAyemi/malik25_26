module sky130_fd_sc_ls__ha_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic SUM,
    input logic COUT
);

    // SUM is the XOR of A and B.
    check_sum_is_xor: assert property (
        @(posedge clk) SUM == (A ^ B)
    );

    // COUT is the AND of A and B.
    check_cout_is_and: assert property (
        @(posedge clk) COUT == (A & B)
    );

    // Both low inputs produce a low sum and no carry.
    check_zero_inputs: assert property (
        @(posedge clk) (!A && !B) |-> (!SUM && !COUT)
    );

    // A low and B high produce a high sum and no carry.
    check_a_low_b_high: assert property (
        @(posedge clk) (!A && B) |-> (SUM && !COUT)
    );

    // A high and B low produce a high sum and no carry.
    check_a_high_b_low: assert property (
        @(posedge clk) (A && !B) |-> (SUM && !COUT)
    );

    // Both high inputs produce a high carry and low sum.
    check_one_inputs: assert property (
        @(posedge clk) (A && B) |-> (COUT && !SUM)
    );

endmodule