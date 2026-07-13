module sky130_fd_sc_hd__fah_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B,
    input logic CI
);

    // SUM is the three-input XOR of A, B, and CI.
    check_sum_is_three_input_xor: assert property (
        @(posedge clk) SUM == (A ^ B ^ CI)
    );

    // COUT is high when at least two inputs are high.
    check_cout_is_two_or_more_high: assert property (
        @(posedge clk) COUT == ((A & B) | (A & CI) | (B & CI))
    );

    // COUT is low when fewer than two inputs are high.
    check_cout_is_zero_when_two_or_fewer_low: assert property (
        @(posedge clk) ((~A & ~B) | (~A & ~CI) | (~B & ~CI)) |-> !COUT
    );

    // COUT is high when all three inputs are high.
    check_cout_is_one_when_all_high: assert property (
        @(posedge clk) (A & B & CI) |-> COUT
    );

    // COUT is low when exactly one input is high.
    check_cout_is_zero_when_one_high: assert property (
        @(posedge clk) ((A & ~B & ~CI) | (~A & B & ~CI) | (~A & ~B & CI)) |-> !COUT
    );

    // COUT is low when all three inputs are low.
    check_cout_is_zero_when_all_low: assert property (
        @(posedge clk) (~A & ~B & ~CI) |-> !COUT
    );

endmodule