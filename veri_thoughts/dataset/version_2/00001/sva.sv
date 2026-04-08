module calculator_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic       start,
    input logic [7:0] result
);

    // On each start after the first, result holds the previous addition.
    check_previous_add_result: assert property (
        @(posedge start)
        (($past(start) === 1'b1) && ($past(op) == 2'b00))
        |-> (result == (($past(a) + $past(b)) & 16'h00FF))
    );

    // On each start after the first, result holds the previous subtraction.
    check_previous_sub_result: assert property (
        @(posedge start)
        (($past(start) === 1'b1) && ($past(op) == 2'b01))
        |-> (result == (($past(a) - $past(b)) & 16'h00FF))
    );

    // On each start after the first, result holds the low 8 bits of the previous product.
    check_previous_mul_result: assert property (
        @(posedge start)
        (($past(start) === 1'b1) && ($past(op) == 2'b10))
        |-> (result == (($past(a) * $past(b)) & 16'h00FF))
    );

    // On each start after the first, result holds the previous quotient when divisor was nonzero.
    check_previous_div_result: assert property (
        @(posedge start)
        (($past(start) === 1'b1) && ($past(op) == 2'b11) && ($past(b) != 8'h00))
        |-> (result == ($past(a) / $past(b)))
    );

endmodule