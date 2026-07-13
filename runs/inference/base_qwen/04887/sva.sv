module calculator_sva (
    input logic clk,
    input logic rst_n,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic [7:0] result
);
    // Addition operation should not produce a result greater than 8'hFF
    property p_addition;
        @(posedge clk) disable iff (!rst_n) (op == 2'b00) |-> (result <= 8'hFF);
    endproperty
    add_check: assert property (p_addition) else $error("Addition result out of range");

    // Subtraction operation should not produce a result less than 8'h00
    property p_subtraction;
        @(posedge clk) disable iff (!rst_n) (op == 2'b01) |-> (result >= 8'h00);
    endproperty
    sub_check: assert property (p_subtraction) else $error("Subtraction result out of range");

    // Multiplication result should not exceed 8'hFF
    property p_multiplication;
        @(posedge clk) disable iff (!rst_n) (op == 2'b10) |-> (result <= 8'hFF);
    endproperty
    mul_check: assert property (p_multiplication) else $error("Multiplication result out of range");

    // Division by zero should not occur
    property p_division;
        @(posedge clk) disable iff (!rst_n) (op == 2'b11) |-> (b != 8'h00);
    endproperty
    div_check: assert property (p_division) else $error("Division by zero");

    // Result should be within valid range for all operations
    property p_result_range;
        @(posedge clk) disable iff (!rst_n) |-> (result >= 8'h00) && (result <= 8'hFF);
    endproperty
    range_check: assert property (p_result_range) else $error("Result out of valid range");

    // Reset should drive result to 8'h00
    property p_reset;
        @(posedge clk) disable iff (rst_n) |-> (result == 8'h00);
    endproperty
    reset_check: assert property (p_reset) else $error("Result not reset to 0");

endmodule