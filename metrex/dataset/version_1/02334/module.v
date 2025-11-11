
module SUB_1 #(parameter N = 32)(
    input [N-1:0] A, B,
    output [N:0] D
);

    wire CO;

    assign D[N] = ~CO;

    ADD #(
        .N(N)
    )
    ADD_
    (
        .A(A),
        .B(~B),
        .CI(1'b1),
        .S(D[N-1:0]), 
        .CO(CO)
    );

endmodule
module ADD #(parameter N = 32)(
    input [N-1:0] A, B,
    input CI,
    output [N-1:0] S,
    output CO
);

    assign {CO, S} = A + B + CI;

endmodule