```systemverilog
module bitwise_operations_sva (
    input logic clk,
    input logic rst_n,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [1:0] operation_select,
    input logic [4:0] shift_amount,
    output logic [31:0] result
);
    // Sequential logic for result assignment
    property p_result_assignment;
        @(posedge clk) disable iff (!rst_n) result == (operation_select == 2'b00 ? a & b :
                                                          operation_select == 2'b01 ? a | b :
                                                          operation_select == 2'b10 ? a ^ b :
                                                          a << shift_amount);
    endproperty
    a1: assert property (p_result_assignment) else $error("Result assignment is incorrect");

    // Combinational logic for and_result
    property p_and_result;
        @(posedge clk) disable iff (!rst_n) a & b == and_result;
    endproperty
    a2: assert property (p_and_result) else $error("AND result is incorrect");

    // Combinational logic for or_result
    property p_or_result;
        @(posedge clk) disable iff (!rst_n) a | b == or_result;
    endproperty
    a3: assert property (p_or_result) else $error("OR result is incorrect");

    // Combinational logic for xor_result
    property p_xor_result;
        @(posedge clk) disable iff (!rst_n) a ^ b == xor_result;
    endproperty
    a4: assert property (p_xor_result) else $error("XOR result is incorrect");

    // Combinational logic for shift_result
    property p_shift_result;
        @(posedge clk) disable iff (!rst_n) a << shift_amount == shift_result;
    endproperty
    a5: assert property (p_shift_result) else $error("Shift result is incorrect");

    // Reset behavior
    property p_reset;
        @(posedge clk) disable iff (!rst_n) result == 32'b0;
    endproperty
    a6: assert property (p_reset) else $error("Result is not reset to 0 on reset");

    // Sequential logic for operation_select
    property p_operation_select;
        @(posedge clk) disable iff (!rst_n) operation_select == 2'b00 ? result == a & b :
                                                                   operation_select == 2'b01 ? result == a | b :
                                                                   operation_select == 2'b10 ? result == a ^ b :
                                                                   result == a << shift_amount;
    endproperty
    a7: assert property (p_operation_select) else $error("Operation select is not correctly implemented");

    // Sequential logic for shift_amount
    property p_shift_amount;
        @(posedge clk) disable iff (!rst_n) shift_amount == 5'b00000 ? result == a << 0 :
                                                                   shift_amount == 5'b00001 ? result == a << 1 :
                                                                   shift_amount == 5'b00010 ? result == a << 2 :
                                                                   shift_amount == 5'b00011 ? result == a << 3 :
                                                                   shift_amount == 5'b00100 ? result == a << 4 :
                                                                   shift_amount == 5'b00101 ? result == a << 5 :
                                                                   shift_amount == 5'b00110 ? result == a << 6 :
                                                                   shift_amount == 5'b00111 ? result == a << 7 :
                                                                   shift_amount == 5'b01000 ? result == a << 8 :
                                                                   shift_amount == 5'b01001 ? result == a << 9 :
                                                                   shift_amount == 5'b01010 ? result == a << 10 :
                                                                   shift_amount == 5'b01011 ? result == a << 11 :
                                                                   shift_amount == 5'b01100 ? result == a << 12 :
                                                                   shift_amount == 5'b01101 ? result == a << 13 :
                                                                   shift_amount == 5'b01110 ? result == a << 14 :
                                                                   shift_amount == 5'b01111 ? result == a << 15 :
                                                                   shift_amount == 5'b10000 ? result == a << 16 :
                                                                   shift_amount == 5'b10001 ? result == a << 17 :
                                                                   shift_amount == 5'b10010 ? result == a << 18 :
                                                                   shift_amount == 5'b10011 ? result == a << 19 :
                                                                   shift_amount == 5'b10100 ? result == a << 20 :
                                                                   shift_amount == 5'b10101 ? result == a << 21 :
                                                                   shift_amount == 5'b10110 ? result == a << 22 :
                                                                   shift_amount == 5'b10111 ? result == a << 23 :
                                                                   shift_amount == 5'b11000 ? result == a << 24 :
                                                                   shift_amount == 5'b11001 ? result == a << 25 :
                                                                   shift_amount == 5'b11010 ? result == a << 26 :
                                                                   shift_amount == 5'b11011 ? result == a << 27 :
                                                                   shift_amount == 5'b11100 ? result == a << 28 :
                                                                   shift_amount == 5'b11101 ? result == a << 29 :
                                                                   shift_amount == 5'b11110 ? result == a << 30 :
                                                                   shift_amount == 5'b11111 ? result == a << 31;
    endproperty
    a8: assert property (p_shift_amount) else $error("Shift amount is not correctly implemented");

    // Sequential logic for a
    property p_a;
        @(posedge clk) disable iff (!rst_n) a == a;
    endproperty
    a9: assert property (p_a) else $error("a is not correctly assigned");

    // Sequential logic for b
    property p_b;
        @(posedge clk) disable iff (!rst_n) b == b;
    endproperty
    a10: assert property (p_b) else $error("b is not correctly assigned");
endmodule
```