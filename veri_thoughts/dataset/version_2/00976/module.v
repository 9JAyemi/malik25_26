module adder (
    input [15:0] A,
    input [15:0] B,
    input CIN,
    output [15:0] SUM,
    output COUT
);

    assign {COUT, SUM} = A + B + CIN;

endmodule