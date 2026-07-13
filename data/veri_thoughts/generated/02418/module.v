
module mux_2to1(
    input A,
    input B,
    input S,
    output Y
);

    wire not_S;
    assign not_S = ~S;
    
    wire Y_A;
    wire Y_B;
    
    and gate_A(Y_A, A, not_S);
    and gate_B(Y_B, B, S);
    
    or gate_C(Y, Y_A, Y_B);

endmodule