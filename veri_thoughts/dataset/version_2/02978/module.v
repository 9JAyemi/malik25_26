module and4 (
    input wire A1,
    input wire A2,
    input wire B1,
    input wire B2,
    output wire Y
);

    wire w1, w2, w3;

    and gate1 (w1, A1, A2);
    and gate2 (w2, B1, B2);
    and gate3 (w3, w1, w2);
    assign Y = w3;

endmodule