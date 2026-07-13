module calculator_sva (
    input logic       clk,
    input logic       rst,
    input logic       clear,
    input logic [1:0] op,
    input logic [7:0] num1,
    input logic [7:0] num2,
    input logic [7:0] result
);

    // Reset clears the registered result on the next cycle.
    check_reset_clears_result: assert property (
        @(posedge clk) rst |=> (result == 8'h00)
    );

    // Clear clears the registered result on the next cycle.
    check_clear_clears_result: assert property (
        @(posedge clk) disable iff (rst)
        clear |=> (result == 8'h00)
    );

    // Add operation updates result with the previous cycle sum.
    check_add_updates_result: assert property (
        @(posedge clk) disable iff (rst)
        (!clear && (op == 2'b00)) |=> (result == (($past(num1) + $past(num2)) & 8'hFF))
    );

    // Subtract operation updates result with the previous cycle difference.
    check_sub_updates_result: assert property (
        @(posedge clk) disable iff (rst)
        (!clear && (op == 2'b01)) |=> (result == (($past(num1) - $past(num2)) & 8'hFF))
    );

    // Multiply operation updates result with the truncated previous cycle product.
    check_mul_updates_result: assert property (
        @(posedge clk) disable iff (rst)
        (!clear && (op == 2'b10)) |=> (result == (($past(num1) * $past(num2)) & 8'hFF))
    );

    // Divide operation updates result with the previous cycle quotient when divisor is nonzero.
    check_div_updates_result: assert property (
        @(posedge clk) disable iff (rst)
        (!clear && (op == 2'b11) && (num2 != 8'h00)) |=> (result == (($past(num1) / $past(num2)) & 8'hFF))
    );

endmodule