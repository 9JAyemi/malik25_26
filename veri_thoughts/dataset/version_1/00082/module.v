module top_module(
    input a,
    input b,
    input sel_b1,
    input sel_b2,
    output reg out_always,
    output out_and,
    output out_or,
    output out_xor
);

    wire mux_out;
    wire [3:0] logic_gate_out;

    // 2-to-1 Multiplexer
    assign mux_out = (sel_b1 & sel_b2) ? b : a;

    // 4-input Logic Gate
    and_gate logic_and(.and_out(logic_gate_out[0]), .a(a), .b(b), .c(sel_b1), .d(sel_b2));
    or_gate logic_or(.or_out(logic_gate_out[1]), .a(a), .b(b), .c(sel_b1), .d(sel_b2));
    xor_gate logic_xor(.xor_out(logic_gate_out[2]), .a(a), .b(b), .c(sel_b1), .d(sel_b2));
    assign logic_gate_out[3] = 1'b0;

    // Output assignments
    assign out_and = logic_gate_out[0];
    assign out_or = logic_gate_out[1];
    assign out_xor = logic_gate_out[2];
    always @* begin
        out_always = mux_out;
    end

endmodule

module and_gate(
    output and_out,
    input a,
    input b,
    input c,
    input d
);
    assign and_out = a & b & c & d;
endmodule

module or_gate(
    output or_out,
    input a,
    input b,
    input c,
    input d
);
    assign or_out = a | b | c | d;
endmodule

module xor_gate(
    output xor_out,
    input a,
    input b,
    input c,
    input d
);
    assign xor_out = a ^ b ^ c ^ d;
endmodule