module and_gate (
    input a,
    input b,
    output y
);

    assign y = a & b;

endmodule

module a31oi_2 (
    output Y,
    input A1,
    input A2,
    input A3,
    input B1
);

    wire y1, y2;
    and_gate base (
        .a(A1),
        .b(A2),
        .y(y1)
    );

    and_gate second (
        .a(y1),
        .b(A3),
        .y(y2)
    );

    assign Y = ~(y2 | B1); 

endmodule