module logic_circuit(
    input [1:0] in1,
    input [1:0] in2,
    output [1:0] out
);

    assign out = ~(in1 & in2); 

endmodule