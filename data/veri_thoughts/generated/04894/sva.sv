module binary_adder_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] sum,
    input logic carry_out
);

    // Full output matches the 9-bit addition of A and B.
    check_full_result: assert property (
        @(posedge clk) {carry_out, sum} == ({1'b0, A} + {1'b0, B})
    );

    // sum is the low 8 bits of the addition.
    check_sum_low_bits: assert property (
        @(posedge clk) sum == (({1'b0, A} + {1'b0, B})[7:0])
    );

    // carry_out is the high bit of the addition.
    check_carry_high_bit: assert property (
        @(posedge clk) carry_out == (({1'b0, A} + {1'b0, B})[8])
    );

    // A equal to zero passes B through with no carry.
    check_a_zero_identity: assert property (
        @(posedge clk) (A == 8'h00) |-> ((sum == B) && (carry_out == 1'b0))
    );

    // B equal to zero passes A through with no carry.
    check_b_zero_identity: assert property (
        @(posedge clk) (B == 8'h00) |-> ((sum == A) && (carry_out == 1'b0))
    );

    // FF plus FF produces FE with carry.
    check_ff_plus_ff: assert property (
        @(posedge clk) ((A == 8'hFF) && (B == 8'hFF)) |-> ((sum == 8'hFE) && (carry_out == 1'b1))
    );

endmodule