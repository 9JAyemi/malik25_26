module top_module(
    input wire [7:0] A,
    input wire [7:0] B,
    output wire [7:0] XOR_out,
    output wire OR_out
);

    XOR_module XOR_inst(
        .A(A),
        .B(B),
        .out(XOR_out)
    );

    OR_module OR_inst(
        .in1(XOR_out[0]),
        .in2(XOR_out[1]),
        .out(OR_out)
    );

endmodule

module XOR_module(
    input wire [7:0] A,
    input wire [7:0] B,
    output wire [7:0] out
);

    assign out = {A[0]&~B[0] | ~A[0]&B[0], 
                 A[1]&~B[1] | ~A[1]&B[1], 
                 A[2]&~B[2] | ~A[2]&B[2], 
                 A[3]&~B[3] | ~A[3]&B[3], 
                 A[4]&~B[4] | ~A[4]&B[4], 
                 A[5]&~B[5] | ~A[5]&B[5], 
                 A[6]&~B[6] | ~A[6]&B[6], 
                 A[7]&~B[7] | ~A[7]&B[7]};

endmodule

module OR_module(
    input wire in1,
    input wire in2,
    output wire out
);

    assign out = in1 | in2;

endmodule