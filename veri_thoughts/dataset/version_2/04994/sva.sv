module calculator_sva (
    input logic clk,
    input logic rst,
    input logic [1:0] op,
    input logic [7:0] num1,
    input logic [7:0] num2,
    input logic [7:0] result,
    input logic valid
);

    localparam logic [1:0] ADD = 2'b00;
    localparam logic [1:0] SUB = 2'b01;
    localparam logic [1:0] MUL = 2'b10;
    localparam logic [1:0] DIV = 2'b11;

    // Synchronous reset clears result and valid on the next cycle.
    check_sync_reset_clears_outputs: assert property (
        @(posedge clk) rst |=> ((result == 8'h00) && (valid == 1'b0))
    );

    // Any non-reset cycle drives valid high on the next cycle.
    check_valid_set_after_active_cycle: assert property (
        @(posedge clk) disable iff (rst)
        1'b1 |=> (valid == 1'b1)
    );

    // ADD stores the prior-cycle sum and asserts valid.
    check_add_updates_result: assert property (
        @(posedge clk) disable iff (rst)
        (op == ADD) |=> ((result == (($past(num1) + $past(num2)) & 8'hFF)) && (valid == 1'b1))
    );

    // SUB stores the prior-cycle difference and asserts valid.
    check_sub_updates_result: assert property (
        @(posedge clk) disable iff (rst)
        (op == SUB) |=> ((result == (($past(num1) - $past(num2)) & 8'hFF)) && (valid == 1'b1))
    );

    // MUL stores the low 8 bits of the prior-cycle product and asserts valid.
    check_mul_updates_result: assert property (
        @(posedge clk) disable iff (rst)
        (op == MUL) |=> ((result == (($past(num1) * $past(num2)) & 8'hFF)) && (valid == 1'b1))
    );

    // DIV with a nonzero divisor stores the prior-cycle quotient and asserts valid.
    check_div_updates_result: assert property (
        @(posedge clk) disable iff (rst)
        ((op == DIV) && (num2 != 8'h00)) |=> ((result == (($past(num1) / $past(num2)) & 8'hFF)) && (valid == 1'b1))
    );

endmodule