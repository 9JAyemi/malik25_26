module bitwise_operations_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [1:0]  operation_select,
    input logic [4:0]  shift_amount,
    input logic [31:0] result
);

    // No reset in RTL; sample this combinational DUT on clk.

    // Select 00 computes the combined AND/OR term XORed with a left shift of a.
    check_result_select_00: assert property (
        @(posedge clk)
        (operation_select == 2'b00) |-> (result == (((a & b) & (a | b)) ^ (a << shift_amount)))
    );

    // Select 01 forwards the bitwise AND of a and b.
    check_result_select_01: assert property (
        @(posedge clk)
        (operation_select == 2'b01) |-> (result == (a & b))
    );

    // Select 10 forwards the bitwise OR of a and b.
    check_result_select_10: assert property (
        @(posedge clk)
        (operation_select == 2'b10) |-> (result == (a | b))
    );

    // Select 11 forwards the bitwise XOR of a and b.
    check_result_select_11: assert property (
        @(posedge clk)
        (operation_select == 2'b11) |-> (result == (a ^ b))
    );

endmodule