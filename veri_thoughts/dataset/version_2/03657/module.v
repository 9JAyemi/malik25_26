module xor_gate (
    input  A,
    input  B,
    output Y,
    input  VDD,
    input  VSS
);

wire A_bar, B_bar;
assign A_bar = ~A;
assign B_bar = ~B;

wire Y1, Y2;
assign Y1 = A & B_bar;
assign Y2 = A_bar & B;
assign Y  = Y1 | Y2;

endmodule