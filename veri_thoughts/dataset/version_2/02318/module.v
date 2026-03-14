module and3(
    input A,
    input B,
    input C,
    output X
);

    wire and0_out;
    wire and1_out;

    and2 and0(.A(A), .B(B), .Z(and0_out));
    and2 and1(.A(C), .B(and0_out), .Z(and1_out));

    assign X = and1_out;

endmodule

module and2(input A, input B, output Z);
    assign Z = A & B;
endmodule