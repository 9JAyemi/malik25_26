module top_module (
    input a,
    input b,
    input sel,
    output z
);

    wire mux_out;
    wire xor_in1, xor_in2;
    
    // 2-to-1 multiplexer
    mux_2to1 mux_inst (
        .a(a),
        .b(b),
        .sel(sel),
        .mux_out(mux_out)
    );
    
    // XOR gate
    xor_gate xor_inst (
        .xor_in1(mux_out),
        .xor_in2(sel),
        .xor_out(z)
    );
    
endmodule

module mux_2to1 (
    input a,
    input b,
    input sel,
    output mux_out
);

    assign mux_out = (sel == 1'b0) ? a : b;
    
endmodule

module xor_gate (
    input xor_in1,
    input xor_in2,
    output xor_out
);

    assign xor_out = xor_in1 ^ xor_in2;
    
endmodule