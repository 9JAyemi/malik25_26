module sky130_fd_sc_ls__ha_sva (
    input logic clk,
    input logic COUT,
    input logic SUM,
    input logic A,
    input logic B
);

    // Carry output matches the input AND.
    check_cout_is_and: assert property (
        @(posedge clk) COUT == (A & B)
    );

    // Sum output matches the input XOR.
    check_sum_is_xor: assert property (
        @(posedge clk) SUM == (A ^ B)
    );

    // 0 + 0 produces zero sum and zero carry.
    check_zero_zero_case: assert property (
        @(posedge clk) (!A && !B) |-> (!SUM && !COUT)
    );

    // 1 + 0 produces sum with no carry.
    check_one_zero_case: assert property (
        @(posedge clk) (A && !B) |-> (SUM && !COUT)
    );

    // 0 + 1 produces sum with no carry.
    check_zero_one_case: assert property (
        @(posedge clk) (!A && B) |-> (SUM && !COUT)
    );

    // 1 + 1 produces carry with no sum.
    check_one_one_case: assert property (
        @(posedge clk) (A && B) |-> (!SUM && COUT)
    );

endmodule