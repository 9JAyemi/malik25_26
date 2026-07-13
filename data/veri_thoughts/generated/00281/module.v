
module mult_gate (
    output Y,
    input J,
    input I,
    input H,
    input G,
    input F,
    input E,
    input D,
    input C,
    input B,
    input A
);

    wire w3;
    wire w2;
    wire w1;

    and gate3(w3, I, H, G);
    and gate2(w2, F, E, D);
    and gate1(w1, C, B, A);
    or gate4(Y, w3, w2, w1, J);

endmodule