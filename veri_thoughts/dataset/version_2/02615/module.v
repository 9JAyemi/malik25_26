module combinational_circuit( 
    input [3:0] in,
    output out_and,
    output out_or,
    output out_xor
);

    wire and1, and2, and3, and4, and5, and6;
    wire or1, or2, or3, or4;
    wire xor1, xor2, xor3;
    
    assign and1 = in[0] & in[1];
    assign and2 = in[0] & in[2];
    assign and3 = in[0] & in[3];
    assign and4 = in[1] & in[2];
    assign and5 = in[1] & in[3];
    assign and6 = in[2] & in[3];
    
    assign or1 = in[0] | in[1];
    assign or2 = in[0] | in[2];
    assign or3 = in[0] | in[3];
    assign or4 = in[1] | in[2] | in[3];
    
    assign xor1 = in[0] ^ in[1];
    assign xor2 = in[0] ^ in[2];
    assign xor3 = in[0] ^ in[3];
    
    assign out_and = and1 & and2 & and3 & and4 & and5 & and6;
    assign out_or = or1 | or2 | or3 | or4;
    assign out_xor = xor1 ^ xor2 ^ xor3;
    
endmodule