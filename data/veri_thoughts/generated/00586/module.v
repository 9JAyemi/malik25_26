
module adder16 (
    input [15:0] in1,
    input [15:0] in2,
    output [15:0] out,
    output carry
);

    assign {carry, out} = in1 + in2;

endmodule
module nand16 (
    input [15:0] in1,
    input [15:0] in2,
    output [15:0] out
);

    assign out = ~(in1 & in2);

endmodule
module mux16x2 (
    input [15:0] in1,
    input [15:0] in2,
    input sel,
    output [15:0] out
);

    assign out = (sel == 1'b0) ? in1 : in2;

endmodule
module alu(
    input [15:0] in1, in2,
    input op,
    output [15:0] out,
    output zero, carry
);

    wire [15:0] outAdd, outNand;
    wire carryAdd;

    // Instantiate the adder16 module
    adder16 add1(.in1(in1), .in2(in2), .out(outAdd), .carry(carryAdd));

    // Instantiate the nand16 module
    nand16 nand1(.in1(in1), .in2(in2), .out(outNand));

    // Instantiate the mux16x2 module
    mux16x2 m1(.in1(outAdd), .in2(outNand), .sel(op), .out(out));

    // Perform bitwise NOR on the output
    nor n1(zero, out[15], out[14], out[13], out[12], out[11], out[10], out[9], out[8], out[7], out[6], out[5], out[4], out[3], out[2], out[1], out[0]);

    // Set the carry output based on the operation performed
    assign carry = (op == 0) ? carryAdd : 1'b0;

endmodule