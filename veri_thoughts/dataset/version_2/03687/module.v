
module pipelined_nor_gate(
    input a,
    input b,
    output out
);

reg pipe1, pipe2;

always @(a or b) begin
    pipe1 <= ~(a & b);
end

always @(pipe1) begin
    pipe2 <= ~pipe1;
end

assign out = pipe2;

endmodule

module top_module(
    input a,
    input b,
    output out
);

wire pipe1, pipe2;
pipelined_nor_gate g1(a, b, pipe1);
pipelined_nor_gate g2(pipe1, pipe1, pipe2);
pipelined_nor_gate g3(pipe2, pipe2, out);

endmodule
