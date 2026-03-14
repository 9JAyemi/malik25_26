
module xor_gate(
    input a,
    input b,
    output out
);

assign out = a ^ b;

endmodule

module top_module(
    input a,
    input b,
    output reg out_always_comb
);

wire out_from_xor_gate;

xor_gate xor_gate_inst(
    .a(a),
    .b(b),
    .out(out_from_xor_gate)
);

always @(*)
begin
    out_always_comb = out_from_xor_gate;
end

endmodule
