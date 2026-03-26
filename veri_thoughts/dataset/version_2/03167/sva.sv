module calculator_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] op,
    input logic [7:0] result
);

    // A zero opcode updates result with the previous cycle's sum.
    check_add_operation: assert property (
        @(posedge clk) (op == 8'h00) |=> (result == ($past(a) + $past(b)))
    );

    // A nonzero opcode updates result with the previous cycle's difference.
    check_sub_operation: assert property (
        @(posedge clk) (op != 8'h00) |=> (result == ($past(a) - $past(b)))
    );

    // Result always reflects the previous cycle's selected arithmetic.
    check_result_function: assert property (
        @(posedge clk) 1'b1 |=> (result == (($past(op) == 8'h00) ? ($past(a) + $past(b)) : ($past(a) - $past(b))))
    );

endmodule