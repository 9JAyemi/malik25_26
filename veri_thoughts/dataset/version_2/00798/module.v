module mux_2to1 (
    input [7:0] in1,
    input [7:0] in2,
    input sel,
    output [7:0] out
);

assign out = sel ? in2 : in1;

endmodule