module binary_adder_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic S,
    input logic CO
);

    // Carry matches the implemented AND of A&B and A^B.
    check_carry_equation: assert property (
        @(posedge clk) CO == ((A & B) & (A ^ B))
    );

    // Sum matches the implemented XOR of A^B with CO.
    check_sum_equation: assert property (
        @(posedge clk) S == ((A ^ B) ^ CO)
    );

    // The implemented carry term is mutually exclusive and always low.
    check_carry_always_low: assert property (
        @(posedge clk) CO == 1'b0
    );

    // With carry low, the sum reduces to A XOR B.
    check_sum_reduces_to_xor: assert property (
        @(posedge clk) S == (A ^ B)
    );

endmodule