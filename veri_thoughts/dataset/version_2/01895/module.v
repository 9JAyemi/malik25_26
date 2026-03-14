
module mux2to1(
    input [3:0] in0, in1,
    input sel,
    output [3:0] out
);

    assign out = sel ? in1 : in0; // 2-to-1 multiplexer logic

endmodule