module sum_of_products_sva (
    input logic        clk,
    input logic        rst,
    input logic [7:0]  A,
    input logic [7:0]  B,
    input logic [15:0] Z
);

    // Reset forces Z to zero on the following clock edge.
    check_reset_clears_z: assert property (
        @(posedge clk) rst |=> (Z == 16'd0)
    );

    // Outside reset, Z accumulates the previous product into the previous Z.
    check_accumulates_product: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (Z == ($past(Z) + ($past(A) * $past(B))))
    );

    // If either operand is zero, Z holds its previous value on the next cycle.
    check_zero_operand_holds_z: assert property (
        @(posedge clk) disable iff (rst)
        ((A == 8'd0) || (B == 8'd0)) |=> (Z == $past(Z))
    );

    // If Z is zero, the next value is just the product of the current operands.
    check_zero_z_loads_product: assert property (
        @(posedge clk) disable iff (rst)
        (Z == 16'd0) |=> (Z == ($past(A) * $past(B)))
    );

endmodule