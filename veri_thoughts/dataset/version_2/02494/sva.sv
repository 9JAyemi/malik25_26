module simple_calculator_sva (
    input logic CLK,
    input logic [7:0] operand1,
    input logic [7:0] operand2,
    input logic [1:0] operation,
    input logic [7:0] result
);
    ///// Functional correctness /////
    // For operation==00, result equals lower 8 bits of operand1 + operand2.
    check_add_when_op00: assert property (
        @(posedge CLK) disable iff (1'b0)
            (operation == 2'b00) |-> (result == ({1'b0,operand1} + {1'b0,operand2})[7:0])
    );

    // For operation==01, result equals lower 8 bits of operand1 - operand2.
    check_sub_when_op01: assert property (
        @(posedge CLK) disable iff (1'b0)
            (operation == 2'b01) |-> (result == ({1'b0,operand1} - {1'b0,operand2})[7:0])
    );

    // For operation==10, result equals lower 8 bits of operand1 - operand2.
    check_sub_when_op10: assert property (
        @(posedge CLK) disable iff (1'b0)
            (operation == 2'b10) |-> (result == ({1'b0,operand1} - {1'b0,operand2})[7:0])
    );

    // For operation==11, result equals lower 8 bits of operand1 - operand2.
    check_sub_when_op11: assert property (
        @(posedge CLK) disable iff (1'b0)
            (operation == 2'b11) |-> (result == ({1'b0,operand1} - {1'b0,operand2})[7:0])
    );

    ///// Arithmetic identities (implied by the RTL) /////
    // Addition identity: op==00 and operand2==0 -> result==operand1.
    add_zero_right_identity: assert property (
        @(posedge CLK) disable iff (1'b0)
            (operation == 2'b00 && operand2 == 8'h00) |-> (result == operand1)
    );

    // Addition identity: op==00 and operand1==0 -> result==operand2.
    add_zero_left_identity: assert property (
        @(posedge CLK) disable iff (1'b0)
            (operation == 2'b00 && operand1 == 8'h00) |-> (result == operand2)
    );

    // Subtraction identity: op!=00 and operand2==0 -> result==operand1.
    sub_zero_right_identity: assert property (
        @(posedge CLK) disable iff (1'b0)
            (operation != 2'b00 && operand2 == 8'h00) |-> (result == operand1)
    );

    // Subtraction to zero: op!=00 and operand1==operand2 -> result==0.
    sub_equal_operands_zero: assert property (
        @(posedge CLK) disable iff (1'b0)
            (operation != 2'b00 && operand1 == operand2) |-> (result == 8'h00)
    );

    // Wrap example: op==00 and operand2==8'hFF -> result==(operand1 - 1)[7:0].
    add_ff_wraps_to_minus_one: assert property (
        @(posedge CLK) disable iff (1'b0)
            (operation == 2'b00 && operand2 == 8'hFF) |-> (result == ({1'b0,operand1} - 9'd1)[7:0])
    );

    // Wrap example: op!=00 and operand2==8'hFF -> result==(operand1 + 1)[7:0].
    sub_ff_wraps_to_plus_one: assert property (
        @(posedge CLK) disable iff (1'b0)
            (operation != 2'b00 && operand2 == 8'hFF) |-> (result == ({1'b0,operand1} + 9'd1)[7:0])
    );
endmodule