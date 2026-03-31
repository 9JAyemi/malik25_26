module full_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic CI,
    input logic SUM,
    input logic COUT
);

    // SUM matches the three-input XOR function.
    check_sum_function: assert property (
        @(posedge clk) SUM == (A ^ B ^ CI)
    );

    // COUT matches the three-input majority function.
    check_cout_function: assert property (
        @(posedge clk) COUT == ((A & B) | (B & CI) | (CI & A))
    );

    // All-zero inputs produce zero sum and zero carry.
    check_zero_inputs: assert property (
        @(posedge clk) (!A && !B && !CI) |-> (!SUM && !COUT)
    );

    // Any one-hot input combination produces sum without carry.
    check_one_hot_inputs: assert property (
        @(posedge clk)
        (( A && !B && !CI) ||
         (!A &&  B && !CI) ||
         (!A && !B &&  CI)) |-> (SUM && !COUT)
    );

    // Any two-hot input combination produces carry without sum.
    check_two_hot_inputs: assert property (
        @(posedge clk)
        (( A &&  B && !CI) ||
         ( A && !B &&  CI) ||
         (!A &&  B &&  CI)) |-> (!SUM && COUT)
    );

    // All-one inputs produce sum without carry.
    check_all_one_inputs: assert property (
        @(posedge clk) (A && B && CI) |-> (SUM && !COUT)
    );

endmodule