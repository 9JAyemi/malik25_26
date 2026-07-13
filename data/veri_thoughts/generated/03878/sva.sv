module calculator_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic clear,
    input logic [7:0] result
);

    // clk is the only clock.
    // clear is a synchronous active-high clear.
    // The logic is sequential; op selects add, sub, mul, or div.

    // Clear forces result to zero.
    check_clear_sets_zero: assert property (
        @(posedge clk) disable iff (1'b0)
        clear |=> (result == 8'h00)
    );

    // op=00 updates result with a+b.
    check_add_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (!clear && (op == 2'b00)) |=> (result == (($past(a) + $past(b)) & 8'hFF))
    );

    // op=01 updates result with a-b.
    check_sub_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (!clear && (op == 2'b01)) |=> (result == (($past(a) - $past(b)) & 8'hFF))
    );

    // op=10 updates result with the low 8 bits of a*b.
    check_mul_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (!clear && (op == 2'b10)) |=> (result == (($past(a) * $past(b)) & 8'hFF))
    );

    // op=11 with nonzero b updates result with a/b.
    check_div_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (!clear && (op == 2'b11) && (b != 8'h00)) |=> (result == (($past(a) / $past(b)) & 8'hFF))
    );

endmodule