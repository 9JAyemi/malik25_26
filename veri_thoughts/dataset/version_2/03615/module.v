
module top_module(
    input a, 
    input b,
    output wire out_behavioral,
    output wire out_structural
);

wire p1_out, p2_out;

// Behavioral XOR gate
assign out_behavioral = a ^ b;

// Structural XOR gate using pipeline approach
xor_gate p1(.a(a), .b(b), .out(p1_out));
xor_gate p2(.a(p1_out), .b(b), .out(p2_out));
assign out_structural = p2_out;

endmodule

module xor_gate(
    input a,
    input b,
    output out
);

assign out = a ^ b;

endmodule
