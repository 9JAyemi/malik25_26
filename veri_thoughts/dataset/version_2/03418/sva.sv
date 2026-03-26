module add4_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic cin,
    input logic [3:0] sum,
    input logic cout
);

    // Combined outputs match 4-bit addition with carry-in.
    check_extended_sum_matches_addition: assert property (
        @(posedge clk) {cout, sum} == ({1'b0, a} + {1'b0, b} + {4'b0000, cin})
    );

    // The least-significant sum bit matches the first full-adder stage.
    check_lsb_sum_equation: assert property (
        @(posedge clk) sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Zero plus zero with no carry-in produces zero and no carry-out.
    check_zero_addition: assert property (
        @(posedge clk)
        (a == 4'b0000 && b == 4'b0000 && cin == 1'b0)
        |-> (sum == 4'b0000 && cout == 1'b0)
    );

    // Adding zero with no carry-in passes a through unchanged.
    check_a_passthrough_when_b_zero: assert property (
        @(posedge clk)
        (b == 4'b0000 && cin == 1'b0)
        |-> (sum == a && cout == 1'b0)
    );

    // Adding zero with no carry-in passes b through unchanged.
    check_b_passthrough_when_a_zero: assert property (
        @(posedge clk)
        (a == 4'b0000 && cin == 1'b0)
        |-> (sum == b && cout == 1'b0)
    );

    // A carry-in propagates through all four bits when a is all ones and b is zero.
    check_full_carry_propagation_from_cin: assert property (
        @(posedge clk)
        (a == 4'b1111 && b == 4'b0000 && cin == 1'b1)
        |-> (sum == 4'b0000 && cout == 1'b1)
    );

    // The maximum input case produces all ones with carry-out asserted.
    check_maximum_addition_case: assert property (
        @(posedge clk)
        (a == 4'b1111 && b == 4'b1111 && cin == 1'b1)
        |-> (sum == 4'b1111 && cout == 1'b1)
    );

endmodule