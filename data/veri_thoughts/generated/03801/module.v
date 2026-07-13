module mux2to1 (
    input I0,
    input I1,
    input S,
    output reg Y
);

    always @ (*) begin
        if (S == 1'b0)
            Y = I0;
        else
            Y = I1;
    end

endmodule

module mux4to1(
    input D0,
    input D1,
    input D2,
    input D3,
    input S0,
    input S1,
    output Y
);

    wire w1, w2, w3;
    
    mux2to1 m1 (
        .I0(D0),
        .I1(D1),
        .S(S0),
        .Y(w1)
    );

    mux2to1 m2 (
        .I0(D2),
        .I1(D3),
        .S(S0),
        .Y(w2)
    );

    mux2to1 m3 (
        .I0(w1),
        .I1(w2),
        .S(S1),
        .Y(w3)
    );

    assign Y = w3;

endmodule