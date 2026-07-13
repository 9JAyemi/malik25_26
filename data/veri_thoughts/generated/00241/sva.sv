module adder_4bit_carry_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);

    // Combined outputs must match the 5-bit addition of a, b, and cin.
    check_full_add_result: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + cin)
    );

    // Sum must match the lower 4 bits of the addition result.
    check_sum_lower_bits: assert property (
        @(posedge clk) {1'b0, sum} == (({1'b0, a} + {1'b0, b} + cin) & 5'h0F)
    );

    // Carry-out must indicate whether the addition result exceeds 4 bits.
    check_carry_overflow: assert property (
        @(posedge clk) cout == (({1'b0, a} + {1'b0, b} + cin) >= 5'd16)
    );

    // Zero inputs must produce a zero sum and no carry.
    check_zero_addition: assert property (
        @(posedge clk) (a == 4'h0 && b == 4'h0 && cin == 1'b0) |-> (sum == 4'h0 && cout == 1'b0)
    );

    // Maximum inputs with carry-in must produce 0xF with carry-out asserted.
    check_max_addition: assert property (
        @(posedge clk) (a == 4'hF && b == 4'hF && cin == 1'b1) |-> (sum == 4'hF && cout == 1'b1)
    );

endmodule