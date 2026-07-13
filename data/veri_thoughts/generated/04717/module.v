module half_adder (
    input A,
    input B,
    output SUM,
    output COUT
);

    assign SUM = A ^ B;
    assign COUT = A & B;

endmodule