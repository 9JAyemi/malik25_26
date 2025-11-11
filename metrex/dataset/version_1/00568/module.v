
module top_module(
    input [7:0] a,
    input [7:0] b,
    input select, // Select input to choose between addition and subtraction
    output [7:0] out // 8-bit output from the functional module
);

// Instantiate the priority encoder module
wire [2:0] pos;
priority_encoder pe(
    .in(a + b), // Input to the priority encoder is the sum of a and b
    .out(pos) // Output of the priority encoder is the position of the first high bit in the sum
);

// Instantiate the adder-subtractor module
wire [7:0] sum;
adder_subtractor as(
    .a(a),
    .b(b),
    .select(select),
    .out(sum) // Output of the adder-subtractor is the sum or difference of a and b
);

// Instantiate the functional module
functional_module fm(
    .pe_out(pos),
    .as_out(sum),
    .out(out)
);

endmodule

module priority_encoder(
    input [7:0] in,
    output [2:0] out
);

assign out = (in[7] ? 7 :
             (in[6] ? 6 :
             (in[5] ? 5 :
             (in[4] ? 4 :
             (in[3] ? 3 :
             (in[2] ? 2 :
             (in[1] ? 1 :
             (in[0] ? 0 : 0))))))));

endmodule

module adder_subtractor(
    input [7:0] a,
    input [7:0] b,
    input select,
    output [7:0] out
);

assign out = select ? a - b : a + b;

endmodule

module functional_module(
    input [2:0] pe_out,
    input [7:0] as_out,
    output [7:0] out
);

assign out = (as_out == 0) ? 0 : pe_out;

endmodule
