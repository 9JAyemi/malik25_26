module binary_adder(A, B, C);
    input [3:0] A, B;
    output [3:0] C;
    
    wire [3:0] s;
    wire [4:0] cout;
    
    fadd a0(A[0], B[0], 1'b0, s[0], cout[1]);
    fadd a1(A[1], B[1], cout[1], s[1], cout[2]);
    fadd a2(A[2], B[2], cout[2], s[2], cout[3]);
    fadd a3(A[3], B[3], cout[3], s[3], cout[4]);
    
    assign C = s;
    
endmodule

module fadd(a, b, cin, s, cout);
    input a, b, cin;
    output s, cout;
    
    assign s = a ^ b ^ cin;
    assign cout = (a & b) | (a & cin) | (b & cin);
    
endmodule