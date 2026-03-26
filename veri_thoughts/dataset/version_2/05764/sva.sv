module calculator_sva (
    input logic clk,
    input logic reset,
    input logic [1:0] op,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] result
);

    // After reset deasserts, the sampled result is still zero.
    check_reset_release_zero: assert property (
        @(posedge clk) disable iff (reset)
        $fell(reset) |-> (result == 8'h00)
    );

    // op 00 loads the sum of a and b into result.
    check_addition_result: assert property (
        @(posedge clk) disable iff (reset)
        (op == 2'b00) |=> (result == (($past(a) + $past(b)) & 16'h00ff))
    );

    // op 01 loads the difference of a and b into result.
    check_subtraction_result: assert property (
        @(posedge clk) disable iff (reset)
        (op == 2'b01) |=> (result == (($past(a) - $past(b)) & 16'h00ff))
    );

    // op 10 loads the low 8 bits of the product of a and b into result.
    check_multiplication_result: assert property (
        @(posedge clk) disable iff (reset)
        (op == 2'b10) |=> (result == (($past(a) * $past(b)) & 16'h00ff))
    );

    // op 11 loads the quotient of a divided by b when b is nonzero.
    check_division_result: assert property (
        @(posedge clk) disable iff (reset)
        ((op == 2'b11) && (b != 8'h00)) |=> (result == ($past(a) / $past(b)))
    );

endmodule