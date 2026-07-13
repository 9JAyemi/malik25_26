module twos_complement(
    input [3:0] a,
    output [3:0] b
);

reg [3:0] c;

assign b = ~a + 1;

always @* c = a;

endmodule