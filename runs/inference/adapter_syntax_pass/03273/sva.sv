module bitwise_operations_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [1:0]  operation_select,
    input logic [4:0]  shift_amount,
    input logic [31:0] result
);

    // Result must match the selected operation.
    check_result_matches_selected_operation: assert property (
        @(posedge clk)
        result == ((operation_select == 2'b00) ? (a & b) :
                   (operation_select == 2'b01) ? (a | b) :
                   (operation_select == 2'b10) ? (a ^ b) :
                                                 (a << shift_amount))
    );

    // Select 00 drives the AND result.
    check_and_operation: assert property (
        @(posedge clk)
        (operation_select == 2'b00) |-> (result == (a & b))
    );

    // Select 01 drives the OR result.
    check_or_operation: assert property (
        @(posedge clk)
        (operation_select == 2'b01) |-> (result == (a | b))
    );

    // Select 10 drives the XOR result.
    check_xor_operation: assert property (
        @(posedge clk)
        (operation_select == 2'b10) |-> (result == (a ^ b))
    );

    // Select 11 drives the left shift result.
    check_shift_operation: assert property (
        @(posedge clk)
        (operation_select == 2'b11) |-> (result == (a << shift_amount))
    );

endmodule