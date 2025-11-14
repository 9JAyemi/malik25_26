
module top_module (
    input [1:0] in,    // Input for the 2-to-4 decoder
    input [3:0] a,    // Input A for the adder-subtractor
    input [3:0] b,    // Input B for the adder-subtractor
    input sub,         // Subtraction flag for the adder-subtractor
    output [3:0] q,    // Output from the functional module
    output overflow   // Overflow output from the adder-subtractor
);

    // 2-to-4 decoder module
    wire [3:0] dec_out;
    decoder_2to4 dec(
        .in(in),
        .out(dec_out)
    );

    // Adder-subtractor module
    wire [3:0] addsub_out;
    wire addsub_overflow;
    adder_subtractor addsub(
        .a(a),
        .b(b),
        .sub(sub),
        .q(addsub_out),
        .overflow(addsub_overflow)
    );

    // Functional module
    assign q = (dec_out[0] == 1'b0) ? addsub_out : 4'b0;
    assign overflow = (dec_out[0] == 1'b0) ? addsub_overflow : (dec_out[1] || dec_out[2] || dec_out[3]);

endmodule
module decoder_2to4 (
    input [1:0] in,    // Input for the 2-to-4 decoder
    output [3:0] out   // Output from the 2-to-4 decoder
);

    assign out[0] = ~in[0] & ~in[1];
    assign out[1] = ~in[0] &  in[1];
    assign out[2] =  in[0] & ~in[1];
    assign out[3] =  in[0] &  in[1];

endmodule
module adder_subtractor (
    input [3:0] a,    // Input A for the adder-subtractor
    input [3:0] b,    // Input B for the adder-subtractor
    input sub,         // Subtraction flag for the adder-subtractor
    output [3:0] q,    // Output from the adder-subtractor
    output overflow   // Overflow output from the adder-subtractor
);

    // Intermediate sum
    wire [4:0] sum = (sub) ? (a - b) : (a + b);
    
    // Assign q and overflow
    assign q = sum[3:0];
    assign overflow = sum[4];

endmodule