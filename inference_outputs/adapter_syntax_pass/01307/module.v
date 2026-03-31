
module top_module (
    input clk,
    input [15:0] A,
    input [15:0] B,
    input [3:0] SEL,
    output [15:0] result
);

wire [15:0] add_sub_out;
wire [15:0] shift_out;

// Include the actual modules
adder_subtractor add_sub(.A(A), .B(B), .sub(SEL[0]), .out(add_sub_out));
barrel_shifter shift(.A(A), .B(B), .dir(SEL[0]), .out(shift_out));

// Determine the output based on the selection signal
assign result = (SEL[1]) ? shift_out : add_sub_out;

endmodule

module adder_subtractor (
    input [15:0] A,
    input [15:0] B,
    input sub, // Control signal for subtraction (0 for addition, 1 for subtraction)
    output [15:0] out
);

// Perform the addition or subtraction based on the control signal
assign out = (sub) ? (A - B) : (A + B);

endmodule

module barrel_shifter (
    input [15:0] A,
    input [15:0] B,
    input dir, // Shift direction control signal (0 for left shift, 1 for right shift)
    output [15:0] out
);

// Barrel shifter implementation

// Determine the shift direction and perform the shifting operation
assign out = (dir) ? (A >> B) : (A << B);

endmodule
