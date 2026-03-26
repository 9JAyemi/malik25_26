module my_module (
    Y,
    A1,
    A2,
    A3,
    A4,
    B1
);

    output Y;
    input A1;
    input A2;
    input A3;
    input A4;
    input B1;

    wire and1;
    wire and2;
    wire or1;
    wire and3;
    wire not1;
    wire not2;

    assign and1 = A1 & A2;
    assign and2 = A3 & A4;
    assign or1 = B1 | and1;
    assign and3 = not2 & or1;
    assign not1 = ~A3;
    assign not2 = ~not1;
    
    o41ai_2 base (
        .Y(Y),
        .A1(and1),
        .A2(and2),
        .A3(not1),
        .A4(A4),
        .B1(and3)
    );

endmodule

module o41ai_2 (
    input A1,
    input A2,
    input A3,
    input A4,
    input B1,
    output Y
);

    wire and1_result;
    wire and2_result;
    wire and2_inverted;
    wire or_result;

    // Hypothetical functionality based on the name
    assign and1_result = A1 & A2;
    assign and2_result = A3 & A4;
    assign and2_inverted = ~and2_result;
    assign or_result = and1_result | and2_inverted;
    assign Y = or_result & B1;

endmodule
