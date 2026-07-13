module arithmetic_op_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] ctrl,
    input logic [7:0] result
);

// Addition mode drives result to a + b.
    check_add_result: assert property (
        @(posedge clk) (ctrl == 2'b00) |-> (result == (a + b))
    );

// Subtraction mode drives result to a - b.
    check_sub_result: assert property (
        @(posedge clk) (ctrl == 2'b01) |-> (result == (a - b))
    );

// XOR mode drives result to a ^ b.
    check_xor_result: assert property (
        @(posedge clk) (ctrl == 2'b10) |-> (result == (a ^ b))
    );

// Invalid control values drive result to zero.
    check_default_zero: assert property (
        @(posedge clk) (ctrl == 2'b11) |-> (result == 8'h00)
    );

// Zero on b passes a through for addition.
    check_add_zero_b_passthrough: assert property (
        @(posedge clk) (ctrl == 2'b00 && b == 8'h00) |-> (result == a)
    );

// Zero on b passes a through for subtraction.
    check_sub_zero_b_passthrough: assert property (
        @(posedge clk) (ctrl == 2'b01 && b == 8'h00) |-> (result == a)
    );

// Zero on a passes b through for subtraction.
    check_sub_zero_a_passthrough: assert property (
        @(posedge clk) (ctrl == 2'b01 && a == 8'h00) |-> (result == ~b)
    );

// Zero on a and b produce zero for XOR.
    check_xor_zero_inputs: assert property (
        @(posedge clk) (ctrl == 2'b10 && a == 8'h00 && b == 8'h00) |-> (result == 8'h00)
    );

// Zero on a and b produce zero for addition.
    check_add_zero_inputs: assert property (
        @(posedge clk) (ctrl == 2'b00 && a == 8'h00 && b == 8'h00) |-> (result == 8'h00)
    );

// Zero on a and b produce zero for subtraction.
    check_sub_zero_inputs: assert property (
        @(posedge clk) (ctrl == 2'b01 && a == 8'h00 && b == 8'h00) |-> (result == 8'h00)
    );

endmodule
