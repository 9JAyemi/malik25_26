module bitwise_and (
    input [3:0] in1,
    input [3:0] in2,
    output [3:0] out,
    input VPWR, VGND, VPB, VNB
);

wire [3:0] not_in1;
wire [3:0] not_in2;
wire [3:0] not_out;

// invert the inputs
assign not_in1 = ~in1;
assign not_in2 = ~in2;

// perform the OR operation on the inverted inputs
assign not_out[0] = not_in1[0] | not_in2[0];
assign not_out[1] = not_in1[1] | not_in2[1];
assign not_out[2] = not_in1[2] | not_in2[2];
assign not_out[3] = not_in1[3] | not_in2[3];

// invert the output of the OR gate to get the AND result
assign out = ~not_out;

endmodule