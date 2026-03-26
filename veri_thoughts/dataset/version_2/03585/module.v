
module xor_gate(
    input a,
    input b,
    output wire xor_out
);

assign xor_out = a ^ b;

endmodule

module functional_module(
    input xor_out,
    output reg func_out
);

always @(*) begin
    if(xor_out == 1'b1) begin
        func_out = 1'b1;
    end else begin
        func_out = 1'b0;
    end
end

endmodule

module control_logic(
    input a,
    input b,
    input select,
    output reg out
);

wire xor_out;
wire func_out;

xor_gate xor_inst(
    .a(a),
    .b(b),
    .xor_out(xor_out)
);

functional_module func_inst(
    .xor_out(xor_out),
    .func_out(func_out)
);

always @(*) begin
    if(select == 1'b1) begin
        out = func_out;
    end else begin
        out = xor_out;
    end
end

endmodule

module top_module(
    input a, 
    input b,
    input select,
    output wire out
);

control_logic control_inst(
    .a(a),
    .b(b),
    .select(select),
    .out(out)
);

endmodule
