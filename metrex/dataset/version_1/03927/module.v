
module xor_gate(
    input a,
    input b,
    output wire out
);

    assign out = a ^ b;

endmodule

module top_module(
    input a, 
    input b,
    output out_behavioral,
    output out_structural
);

    // Behavioral approach
    wire behavioral_out;
    assign behavioral_out = a ^ b;
    assign out_behavioral = behavioral_out;
    
    // Structural approach
    xor_gate xor_inst(
        .a(a),
        .b(b),
        .out(out_structural)
    );

endmodule
