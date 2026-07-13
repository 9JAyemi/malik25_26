module top_module(
    input a,
    input b,
    input c,
    output out
);

    wire nand_out;
    wire xor_out;
    wire final_out;

    // Connect two input ports to the NAND gate
    nand_gate nand1(
        .a(a),
        .b(b),
        .out(nand_out)
    );

    // Connect the third input port to the XOR gate
    xor_gate xor1(
        .a(nand_out),
        .b(c),
        .out(xor_out)
    );

    // Design an additional functional module that performs a bitwise OR operation
    or_gate or1(
        .a(nand_out),
        .b(xor_out),
        .out(final_out)
    );

    // Connect the final output to the output port
    assign out = final_out;

endmodule

// Define the NAND gate module
module nand_gate(
    input a,
    input b,
    output out
);

    assign out = ~(a & b);

endmodule

// Define the XOR gate module
module xor_gate(
    input a,
    input b,
    output out
);

    assign out = a ^ b;

endmodule

// Define the OR gate module
module or_gate(
    input a,
    input b,
    output out
);

    assign out = a | b;

endmodule