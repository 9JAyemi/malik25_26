
module four_input_or_gate (
    input [3:0] A,
    input [3:0] B,
    input [3:0] C,
    input [3:0] D,
    input VPWR,
    input VGND,
    input VPB,
    input VNB,
    output X
);

    wire [3:0] AB;
    wire [3:0] CD;
    wire [3:0] ABCD;

    assign AB = A | B;
    assign CD = C | D;
    assign ABCD = AB | CD;
    assign X = ABCD[0] | ABCD[1] | ABCD[2] | ABCD[3];

endmodule