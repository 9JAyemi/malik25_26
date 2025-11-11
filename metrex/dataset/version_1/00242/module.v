
module four_input_OR (
    X,
    A,
    B,
    C,
    D
);

    output X;
    input  A;
    input  B;
    input  C;
    input  D;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    wire AB, CD, ABCD;

    // Implement OR operation using combinational logic
    assign AB = A | B;
    assign CD = C | D;
    assign ABCD = AB | CD;
    assign X = ABCD;

endmodule
