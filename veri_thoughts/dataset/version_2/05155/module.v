module and_gate (
    input  a,
    input  b,
    output y
);
    assign y = a & b;
endmodule

module and_comb (
    input  A1,
    input  A2,
    input  B1,
    input  B2,
    output X
);

    wire a1_a2, b1_b2;
    and_gate and1(.a(A1), .b(A2), .y(a1_a2));
    and_gate and2(.a(B1), .b(B2), .y(b1_b2));
    and_gate and3(.a(a1_a2), .b(b1_b2), .y(X));

endmodule