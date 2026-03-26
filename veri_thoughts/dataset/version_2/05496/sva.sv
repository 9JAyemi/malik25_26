module FULL_ADDER_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic CIN,
    input logic S,
    input logic COUT
);

    // Sum output matches the XOR of the three inputs.
    check_sum_function: assert property (
        @(posedge clk) S == (A ^ B ^ CIN)
    );

    // Carry output matches the implemented generate/propagate logic.
    check_cout_function: assert property (
        @(posedge clk) COUT == ((A & B) | (CIN & (A ^ B)))
    );

    // All-zero inputs produce zero sum and zero carry.
    check_all_zero_case: assert property (
        @(posedge clk) (!A && !B && !CIN) |-> (!S && !COUT)
    );

    // Any one-hot input combination produces sum only.
    check_one_hot_case: assert property (
        @(posedge clk) $onehot({A, B, CIN}) |-> (S && !COUT)
    );

    // Any two-high input combination produces carry only.
    check_two_high_case: assert property (
        @(posedge clk) ((A && B && !CIN) || (A && CIN && !B) || (B && CIN && !A)) |-> (!S && COUT)
    );

    // All-high inputs produce both sum and carry.
    check_all_high_case: assert property (
        @(posedge clk) (A && B && CIN) |-> (S && COUT)
    );

endmodule