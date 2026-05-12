
module top_module (
    input [3:0] binary_input, // 4-bit binary input
    input [1:0] shift_amount, // 2-bit shift amount input
    output [3:0] shifted_gray_code_output // 4-bit shifted Gray code output
);

wire [3:0] gray_code_output;

gray_code gray_code_inst (
    .in(binary_input),
    .out(gray_code_output)
);

barrel_shifter barrel_shifter_inst (
    .data(gray_code_output),
    .shift_amount(shift_amount),
    .result(shifted_gray_code_output)
);

endmodule

module gray_code (
    input [3:0] in,
    output [3:0] out
);

assign out[3] = in[3];
assign out[2] = in[3] ^ in[2];
assign out[1] = in[2] ^ in[1];
assign out[0] = in[1] ^ in[0];

endmodule

module barrel_shifter (
    input [3:0] data,
    input [1:0] shift_amount,
    output [3:0] result
);

assign result = (shift_amount == 2'b00) ? data :
               (shift_amount == 2'b01) ? {data[2:0], data[3]} :
               (shift_amount == 2'b10) ? {data[1:0], data[3:2]} :
               {data[0], data[3:1]};

endmodule
