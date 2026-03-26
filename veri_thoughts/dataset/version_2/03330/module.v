
module top_module (
    input [31:0] a, // 32-bit input for adder
    input [31:0] b, // 32-bit input for adder
    input select, // Select input to choose between decoder and functional module
    output [7:0] out // 8-bit output from the active module
);

    wire [31:0] sum; // 32-bit sum output from the adder
    wire [7:0] upper_byte; // 8-bit upper byte output from the decoder
    wire [7:0] lower_byte; // 8-bit lower byte output from the decoder
    wire [7:0] product; // 8-bit product output from the functional module

    carry_select_adder adder(.a(a), .b(b), .sum(sum)); // Instantiate the carry select adder module
    decoder_mux_16bit decoder(.in(sum[15:0]), .upper_byte(upper_byte), .lower_byte(lower_byte)); // Instantiate the decoder and multiplexer module
    functional_module func(.a(upper_byte), .b(lower_byte), .out(product)); // Instantiate the functional module

    assign out = select ? product : {upper_byte, lower_byte}; // Multiplexer to select between decoder and functional module based on select input

endmodule
module carry_select_adder (
    input [31:0] a, // 32-bit input A
    input [31:0] b, // 32-bit input B
    output [31:0] sum // 32-bit sum output
);

    wire [15:0] sum_low, sum_high; // 16-bit lower and upper parts of the sum
    wire carry_out_low, carry_out_high; // Carry outputs from the lower and upper adders

    ripple_adder adder_low(.a(a[15:0]), .b(b[15:0]), .sum(sum_low), .carry_out(carry_out_low)); // Lower 16-bit adder
    ripple_adder adder_high(.a(a[31:16]), .b(b[31:16]), .sum(sum_high), .carry_out(carry_out_high)); // Upper 16-bit adder

    assign sum[15:0] = carry_out_low ? sum_high : sum_low; // Select the correct lower 16 bits of the sum
    assign sum[31:16] = carry_out_high ? sum_high + 1 : sum_high; // Select the correct upper 16 bits of the sum

endmodule
module ripple_adder (
    input [15:0] a, // 16-bit input A
    input [15:0] b, // 16-bit input B
    output [15:0] sum, // 16-bit sum output
    output carry_out // Carry output
);

    assign {carry_out, sum} = a + b;

endmodule
module decoder_mux_16bit (
    input [15:0] in, // 16-bit input
    output [7:0] upper_byte, // 8-bit upper byte output
    output [7:0] lower_byte // 8-bit lower byte output
);

    assign upper_byte = in[15:8];
    assign lower_byte = in[7:0];

endmodule
module functional_module (
    input [7:0] a, // 8-bit input A
    input [7:0] b, // 8-bit input B
    output [7:0] out // 8-bit product output
);

    assign out = a * b;

endmodule