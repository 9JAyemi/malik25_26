module four_bit_adder_assertions (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic C_in,
    input logic clk,
    input logic [3:0] S,
    input logic C_out
);

    // Outputs register the previous cycle's 5-bit addition result.
    check_registered_sum_and_carry: assert property (
        @(posedge clk) 1'b1 |=> ({C_out, S} == $past({1'b0, A} + {1'b0, B} + C_in))
    );

    // Zero inputs produce a zero result on the next clock.
    check_zero_addition: assert property (
        @(posedge clk) (A == 4'h0 && B == 4'h0 && C_in == 1'b0) |=> ({C_out, S} == 5'h00)
    );

    // 15 + 0 + 1 produces a carry-out and zero sum on the next clock.
    check_single_carry_case: assert property (
        @(posedge clk) (A == 4'hF && B == 4'h0 && C_in == 1'b1) |=> ({C_out, S} == 5'h10)
    );

    // The maximum input combination produces 31 on the next clock.
    check_maximum_sum_case: assert property (
        @(posedge clk) (A == 4'hF && B == 4'hF && C_in == 1'b1) |=> ({C_out, S} == 5'h1F)
    );

endmodule