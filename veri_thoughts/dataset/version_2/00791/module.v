
module xor_pipeline(
    input a,
    input b,
    output reg out
);

reg a_reg, b_reg;

always @(*) begin
    a_reg <= a;
    b_reg <= b;
end

always @(*) begin
    out <= a_reg ^ b_reg;
end

endmodule
module top_module(
    input a,
    input b,
    output reg out
);

xor_pipeline xor_inst(
    .a(a),
    .b(b),
    .out(out)
);

endmodule