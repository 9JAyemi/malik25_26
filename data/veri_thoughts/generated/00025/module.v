module pipelined_xor_gate(input a, b, clk, output out);

reg a_reg, b_reg, a_reg1, b_reg1;
wire xor_out, xor_out1;

assign out = xor_out1;

// Pipeline stage 1
always @(posedge clk) begin
    a_reg1 <= a_reg;
    b_reg1 <= b_reg;
end

// Pipeline stage 2
always @(posedge clk) begin
    a_reg <= a;
    b_reg <= b;
end

// XOR gate
assign xor_out = a_reg ^ b_reg;
assign xor_out1 = a_reg1 ^ b_reg1;

endmodule