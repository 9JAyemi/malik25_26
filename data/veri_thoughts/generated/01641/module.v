
module top_module (
    input clk,
    input signed [31:0] a,
    input signed [31:0] b,
    input [7:0] input1,
    input [7:0] input2,
    input control,
    output [1:0] result,
    output signed [31:0] sum
);

    wire signed [15:0] mul8_out;
    wire and_gate_out;
    wire or_gate_out;

    mul8 mul8_inst (
        .a(input1),
        .b(input2),
        .product(mul8_out)
    );

    and_gate and_gate_inst (
        .a(input1[0] & input2[0]),
        .b(input1[1] & input2[1]),
        .out(and_gate_out)
    );

    reg [1:0] result_reg;
    reg [31:0] sum_reg;
    reg or_gate_out_reg;

    always @ (posedge clk) begin
        case (control)
            0: result_reg <= {and_gate_out, 1'b0};
            1: result_reg <= {or_gate_out, 1'b0};
        endcase
        sum_reg <= a + b + {16'd0, mul8_out};
        or_gate_out_reg <= input1 | input2;
    end

    assign result = result_reg;
    assign sum = sum_reg;
    assign or_gate_out = or_gate_out_reg;

endmodule

module mul8 (
    input signed [7:0] a,
    input signed [7:0] b,
    output signed [15:0] product
);

    assign product = a * b;

endmodule

module and_gate (
    input a,
    input b,
    output out
);

    assign out = a & b;

endmodule
