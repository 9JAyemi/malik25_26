module mux2to1 (Y, A, B, S);
    output Y;
    input A, B, S;
    assign Y = (S == 1'b0) ? A : B;
endmodule

module mux4to1 (Y, D0, D1, D2, D3, S0, S1);
    output Y;
    input D0, D1, D2, D3, S0, S1;
    wire w1, w2, w3;
    mux2to1 mux1 (.Y(w1), .A(D0), .B(D1), .S(S1));
    mux2to1 mux2 (.Y(w2), .A(D2), .B(D3), .S(S1));
    mux2to1 mux3 (.Y(w3), .A(w1), .B(w2), .S(S0));
    assign Y = w3;
endmodule