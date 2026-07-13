module calculator_sva (
    input logic clk,
    input logic [31:0] A,
    input logic [31:0] B,
    input logic [1:0] sel,
    input logic [31:0] Z
);

    // sel=00 drives the sum.
    check_add_mode: assert property (
        @(posedge clk) (sel == 2'b00) |-> (Z == (A + B))
    );

    // sel=01 drives the difference.
    check_sub_mode: assert property (
        @(posedge clk) (sel == 2'b01) |-> (Z == (A - B))
    );

    // sel=10 drives the low 32 bits of the product.
    check_mul_mode: assert property (
        @(posedge clk) (sel == 2'b10) |-> (Z == (A * B)[31:0])
    );

    // sel=11 with nonzero B drives the quotient.
    check_div_mode_nonzero: assert property (
        @(posedge clk) ((sel == 2'b11) && (B != 32'd0)) |-> (Z == (A / B))
    );

    // sel=11 with zero B drives zero.
    check_div_mode_zero: assert property (
        @(posedge clk) ((sel == 2'b11) && (B == 32'd0)) |-> (Z == 32'd0)
    );

    // Stable inputs keep the output stable.
    check_stable_inputs_stable_output: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(sel)) |-> $stable(Z)
    );

endmodule