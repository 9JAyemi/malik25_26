module top_module (
    input [15:0] a, // Input for the multiplier and adder modules
    input [15:0] b, // Input for the multiplier module
    input sub, // Input for the adder module
    output [31:0] mult_output, // Output from the multiplier module
    output [15:0] sum_output, // Output from the adder module
    output xor_output // Output from the functional module
);

wire [31:0] mult_result;
wire [15:0] add_result;
wire [31:0] xor_result;

multiplier mult_inst (
    .a(a),
    .b(b),
    .product(mult_result)
);

adder add_inst (
    .a(a),
    .b(b),
    .sub(sub),
    .sum(add_result)
);

functional_module func_inst (
    .mult_input(mult_result),
    .add_input(add_result),
    .xor_output(xor_result)
);

assign mult_output = mult_result;
assign sum_output = add_result;
assign xor_output = xor_result[0];

endmodule

module multiplier (
    input [15:0] a,
    input [15:0] b,
    output [31:0] product
);

integer i;
reg [31:0] temp_product;

always @(*) begin
    temp_product = 0;
    for (i = 0; i < 16; i = i + 1) begin
        if (b[i]) begin
            temp_product = temp_product + (a << i);
        end
    end
end

assign product = temp_product;

endmodule

module adder (
    input [15:0] a,
    input [15:0] b,
    input sub,
    output [15:0] sum
);

wire [15:0] b_xor;

assign b_xor = sub ? b ^ 16'hFFFF : b;

adder16 add_inst (
    .a(a),
    .b(b_xor),
    .sum(sum)
);

endmodule

module adder16 (
    input [15:0] a,
    input [15:0] b,
    output [15:0] sum
);

assign sum = a + b;

endmodule

module functional_module (
    input [31:0] mult_input,
    input [15:0] add_input,
    output [31:0] xor_output
);

assign xor_output = mult_input ^ {16'b0, add_input};

endmodule