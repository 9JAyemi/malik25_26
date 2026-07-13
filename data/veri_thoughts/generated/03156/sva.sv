module binary_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       clk,
    input logic [3:0] Z
);

    // Z is the registered 4-bit sum of A and B from the previous clock.
    check_registered_sum: assert property (
        @(posedge clk) 1'b1 |=> (Z == (($past(A) + $past(B)) & 4'hF))
    );

    // Adding zero to zero produces zero on the next clock.
    check_zero_plus_zero: assert property (
        @(posedge clk) (A == 4'h0 && B == 4'h0) |=> (Z == 4'h0)
    );

    // Adding zero on B passes A through to Z on the next clock.
    check_a_plus_zero: assert property (
        @(posedge clk) (B == 4'h0) |=> (Z == $past(A))
    );

    // Adding zero on A passes B through to Z on the next clock.
    check_zero_plus_b: assert property (
        @(posedge clk) (A == 4'h0) |=> (Z == $past(B))
    );

    // Overflow from 4'hF + 4'h1 wraps around in 4 bits.
    check_overflow_wrap_f_plus_1: assert property (
        @(posedge clk) (A == 4'hF && B == 4'h1) |=> (Z == 4'h0)
    );

    // Overflow from 4'hF + 4'hF keeps only the low 4 bits.
    check_overflow_wrap_f_plus_f: assert property (
        @(posedge clk) (A == 4'hF && B == 4'hF) |=> (Z == 4'hE)
    );

endmodule