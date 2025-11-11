
module binary_adder (
    output COUT,
    output SUM,
    input A,
    input B,
    input CI,
    input VPWR,
    input VGND
);

assign SUM = A ^ B ^ CI;
assign COUT = (A & B) | (CI & (A ^ B));

endmodule
module fah (
    output COUT,
    output SUM,
    input A,
    input B,
    input CI,
    input VPWR,
    input VGND
);

assign SUM = A ^ B ^ CI;
assign COUT = (A & B) | (CI & (A ^ B));

endmodule