
module nor3 (
    input A,
    input B,
    input C,
    output Y
);

wire temp1, temp2;

not (temp1, A);
not (temp2, B);
nor (Y, temp1, temp2, C);

endmodule