module simple_multiplier_sva (
    input logic        clk,
    input logic [7:0]  A,
    input logic [7:0]  B,
    input logic [15:0] Z
);

    // Z is the registered product of A and B from the previous clock.
    check_registered_product: assert property (
        @(posedge clk) 1'b1 |=> (Z == $past(A * B))
    );

    // A zero operand produces a zero product on the next clock.
    check_zero_operand: assert property (
        @(posedge clk) ((A == 8'h00) || (B == 8'h00)) |=> (Z == 16'h0000)
    );

    // A value of one on A passes B through on the next clock.
    check_a_is_one: assert property (
        @(posedge clk) (A == 8'h01) |=> (Z == {8'h00, $past(B)})
    );

    // A value of one on B passes A through on the next clock.
    check_b_is_one: assert property (
        @(posedge clk) (B == 8'h01) |=> (Z == {8'h00, $past(A)})
    );

    // Maximum 8-bit operands produce the expected 16-bit product.
    check_max_operands: assert property (
        @(posedge clk) ((A == 8'hFF) && (B == 8'hFF)) |=> (Z == 16'hFE01)
    );

endmodule