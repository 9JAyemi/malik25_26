module top_module(
    input [3:0] a,
    input [3:0] b,
    output [3:0] out
);

wire [3:0] adder_output;
wire [3:0] shift_output;

four_bit_adder adder_inst(
    .a(a),
    .b(b),
    .sum(adder_output)
);

shift_register shift_reg_inst(
    .data_in(adder_output),
    .shift_output(shift_output)
);

xor_output xor_output_inst(
    .shift_data(shift_output),
    .b(b),
    .out(out)
);

endmodule

module four_bit_adder(
    input [3:0] a,
    input [3:0] b,
    output [3:0] sum
);

wire c1, c2, c3;

full_adder fa0(
    .a(a[0]),
    .b(b[0]),
    .cin(1'b0),
    .sum(sum[0]),
    .cout(c1)
);

full_adder fa1(
    .a(a[1]),
    .b(b[1]),
    .cin(c1),
    .sum(sum[1]),
    .cout(c2)
);

full_adder fa2(
    .a(a[2]),
    .b(b[2]),
    .cin(c2),
    .sum(sum[2]),
    .cout(c3)
);

full_adder fa3(
    .a(a[3]),
    .b(b[3]),
    .cin(c3),
    .sum(sum[3]),
    .cout()
);

endmodule

module full_adder(
    input a,
    input b,
    input cin,
    output sum,
    output cout
);

assign sum = a ^ b ^ cin;
assign cout = (a & b) | (a & cin) | (b & cin);

endmodule

module shift_register(
    input [3:0] data_in,
    output [3:0] shift_output
);

reg [3:0] data_reg;

always @(data_in) begin
    data_reg <= {data_in[2:0], data_in[3]};
end

assign shift_output = data_reg;

endmodule

module xor_output(
    input [3:0] shift_data,
    input [3:0] b,
    output [3:0] out
);

assign out = shift_data ^ b;

endmodule