module and_gate_4 (
    input A1,
    input A2,
    input A3,
    input B1,
    input C1,
    output Y
);

wire temp1, temp2, temp3;

and(temp1, A1, A2);
and(temp2, temp1, A3);
and(temp3, temp2, B1);
and(Y, temp3, C1);

endmodule

