module comparator_3bit_assertions (
    input logic clk,
    input logic [2:0] A,
    input logic [2:0] B,
    input logic [1:0] result
);

    // A greater than B produces 01.
    check_a_gt_b_encoding: assert property (
        @(posedge clk) (A > B) |-> (result == 2'b01)
    );

    // Equal inputs produce 00.
    check_a_eq_b_encoding: assert property (
        @(posedge clk) (A == B) |-> (result == 2'b00)
    );

    // A less than B produces 11.
    check_a_lt_b_encoding: assert property (
        @(posedge clk) (A < B) |-> (result == 2'b11)
    );

    // The LSB is high when A and B differ.
    check_result_lsb_matches_inequality: assert property (
        @(posedge clk) (result[0] == (A != B))
    );

    // The MSB is high only when A is less than B.
    check_result_msb_matches_less_than: assert property (
        @(posedge clk) (result[1] == (A < B))
    );

    // The unused encoding 10 is never generated.
    check_no_unused_encoding: assert property (
        @(posedge clk) (result != 2'b10)
    );

    // Stable inputs keep the result stable.
    check_stable_inputs_hold_result: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(result)
    );

endmodule