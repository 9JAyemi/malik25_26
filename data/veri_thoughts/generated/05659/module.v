module and3_gate (
    output Y,
    input A,
    input B,
    input C
);

    wire AB;
    wire BC;
    wire ABC;

    and gate1 (
        AB,
        A,
        B
    );

    and gate2 (
        BC,
        B,
        C
    );

    or gate3 (
        ABC,
        AB,
        BC
    );

    assign Y = ABC;

endmodule