module simple_calc_sva (
    input logic        clk,
    input logic [7:0]  A,
    input logic [7:0]  B,
    input logic [1:0]  op,
    input logic [7:0]  C
);

    // op=00 drives C with the 8-bit sum of A and B.
    check_add_result: assert property (
        @(posedge clk) (op == 2'b00) |-> (C == ((A + B) & 8'hFF))
    );

    // op=01 drives C with the 8-bit difference of A and B.
    check_sub_result: assert property (
        @(posedge clk) (op == 2'b01) |-> (C == ((A - B) & 8'hFF))
    );

    // op=10 drives C with the low 8 bits of the product of A and B.
    check_mul_result: assert property (
        @(posedge clk) (op == 2'b10) |-> (C == ((A * B) & 8'hFF))
    );

    // op=11 with a nonzero divisor drives C with A divided by B.
    check_div_result: assert property (
        @(posedge clk) ((op == 2'b11) && (B != 8'h00)) |-> (C == ((A / B) & 8'hFF))
    );

endmodule