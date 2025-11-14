module ADDER4 (
    input [3:0] A,
    input [3:0] B,
    input CIN,
    output [3:0] SUM,
    output COUT
);

    assign {COUT, SUM} = A + B + CIN;

endmodule