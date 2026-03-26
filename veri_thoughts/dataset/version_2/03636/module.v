module and_gate(
    input A,
    input B,
    input C,
    input D,
    output Y,
    input VPWR,
    input VGND
);

    wire temp1, temp2, temp3;
    and and1 (
        temp1,
        A,
        B
    );
    and and2 (
        temp2,
        temp1,
        C
    );
    and and3 (
        temp3,
        temp2,
        D
    );
    assign Y = temp3;

endmodule