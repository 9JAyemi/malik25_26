
module custom_or_gate (
    input A,
    input B,
    input C,
    output out
);

wire temp;

or (temp, A, B);
and (out, temp, C);

endmodule