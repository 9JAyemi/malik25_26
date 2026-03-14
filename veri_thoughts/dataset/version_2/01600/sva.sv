module simple_calculator_sva (
    input logic clk,             // Sampling clock for assertions (DUT has no clock/reset)
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] opcode,
    input logic [7:0] result
);
    // When opcode==00, result is low 8 bits of a+b.
    check_add_result_low8: assert property (
        @(posedge clk) (opcode == 2'b00) |-> (result == (a + b)[7:0])
    );

    // When opcode==01, result is low 8 bits of a-b.
    check_sub_result_low8: assert property (
        @(posedge clk) (opcode == 2'b01) |-> (result == (a - b)[7:0])
    );

    // When opcode==10, result is low 8 bits of a*b.
    check_mul_result_low8: assert property (
        @(posedge clk) (opcode == 2'b10) |-> (result == (a * b)[7:0])
    );

    // When opcode==11 and b!=0, result is a/b.
    check_div_result_nonzero: assert property (
        @(posedge clk) (opcode == 2'b11 && b != 8'd0) |-> (result == (a / b))
    );

    // If inputs stable and not dividing by zero, result stays stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(a) && $stable(b) && $stable(opcode) && !(opcode == 2'b11 && b == 8'd0)) |-> $stable(result)
    );
endmodule