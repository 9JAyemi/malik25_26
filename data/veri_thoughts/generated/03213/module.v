
module xor_lut (
    input a,
    input b,
    output reg out
);
    always @(*)
    begin
        case ({a,b})
            2'b00: out = 1'b0;
            2'b01: out = 1'b1;
            2'b10: out = 1'b1;
            2'b11: out = 1'b0;
        endcase
    end
endmodule
module bitwise_ops (
    input [1:0] in,
    output [1:0] out_and,
    output [1:0] out_or,
    output [1:0] out_xor
);
    assign out_and = in[1:0] & in[1:0];
    assign out_or = in[1:0] | in[1:0];
    assign out_xor = in[1:0] ^ in[1:0];
endmodule
module final_module (
    input out_lut,
    input [1:0] out_and,
    input [1:0] out_or,
    input [1:0] out_xor,
    output final_output
);
    assign final_output = out_lut | out_and[0] | out_and[1] | out_or[0] | out_or[1] | out_xor[0] | out_xor[1];
endmodule
module top_module (
    input a,
    input b,
    input [1:0] in,
    output reg out_lut,
    output [1:0] out_and,
    output [1:0] out_or,
    output [1:0] out_xor,
    output final_output
);
    wire xor_out;
    wire [1:0] bitwise_and_out;
    wire [1:0] bitwise_or_out;
    wire [1:0] bitwise_xor_out;

    xor_lut xor_inst (
        .a(a),
        .b(b),
        .out(xor_out)
    );

    bitwise_ops bitwise_inst (
        .in(in),
        .out_and(bitwise_and_out),
        .out_or(bitwise_or_out),
        .out_xor(bitwise_xor_out)
    );

    final_module final_inst (
        .out_lut(out_lut),
        .out_and(out_and),
        .out_or(out_or),
        .out_xor(out_xor),
        .final_output(final_output)
    );

    always @(*)
    begin
        out_lut = xor_out;
    end

    assign out_and = bitwise_and_out;
    assign out_or = bitwise_or_out;
    assign out_xor = bitwise_xor_out;
endmodule