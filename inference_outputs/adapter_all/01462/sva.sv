module ripple_adder_sva (
    input logic        clk,
    input logic [7:0]  a,
    input logic [7:0]  b,
    input logic [7:0]  sum,
    input logic        carry_out
);

    // Carry-out matches the MSB of the 9-bit addition.
    check_carry_matches_addition: assert property (
        @(posedge clk) carry_out == (({1'b0, a} + {1'b0, b})[8])
    );

    // Sum matches the low 8 bits of the 9-bit addition.
    check_sum_matches_addition: assert property (
        @(posedge clk) sum == (({1'b0, a} + {1'b0, b})[7:0])
    );

    // Adding zero on b passes a through with no carry.
    check_add_zero_b: assert property (
        @(posedge clk) (b == 8'h00) |-> (sum == a && carry_out == 1'b0)
    );

    // Adding zero on a passes b through with no carry.
    check_add_zero_a: assert property (
        @(posedge clk) (a == 8'h00) |-> (sum == b && carry_out == 1'b0)
    );

    // Adding 8'hFF on b subtracts one from a and clears carry.
    check_add_ff_b: assert property (
        @(posedge clk) (b == 8'hFF) |-> (sum == (a - 8'h01) && carry_out == 1'b0)
    );

    // Adding 8'hFF on a subtracts one from b and clears carry.
    check_add_ff_a: assert property (
        @(posedge clk) (a == 8'hFF) |-> (sum == (b - 8'h01) && carry_out == 1'b0)
    );

    // 8'hFF + 8'hFF produces 8'hFE with carry-out set.
    check_ff_plus_ff: assert property (
        @(posedge clk) (a == 8'hFF && b == 8'hFF) |-> (sum == 8'hFE && carry_out == 1'b1)
    );

    // 0 + 0 produces 0 with no carry.
    check_zero_plus_zero: assert property (
        @(posedge clk) (a == 8'h00 && b == 8'h00) |-> (sum == 8'h00 && carry_out == 1'b0)
    );

    // 8'hFF + 8'h01 produces 8'h00 with carry-out set.
    check_ff_plus_one: assert property (
        @(posedge clk) (a == 8'hFF && b == 8'h01) |-> (sum == 8'h00 && carry_out == 1'b1)
    );

    // 8'h01 + 8'hFF produces 8'h00 with carry-out set.
    check_one_plus_ff: assert property (
        @(posedge clk) (a == 8'h01 && b == 8'hFF) |-> (sum == 8'h00 && carry_out == 1'b1)
    );

endmodule