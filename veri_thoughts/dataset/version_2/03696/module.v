module nor2_gate(
    input A,
    input B_N,
    output Y
    );

    assign Y = ~(A | B_N);
    
endmodule