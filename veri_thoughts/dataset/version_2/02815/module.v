module top_module( 
    input [99:0] in,
    input a,
    input b,
    output out_nor,
    output out_or,
    output out_xor 
);

    // First NAND gate
    wire [99:0] nand1_out;
    assign nand1_out = ~(&in);

    // Second NAND gate
    wire [99:0] nand2_out;
    assign nand2_out = ~(&in);

    // NOR gate output
    wire nor_out;
    assign nor_out = ~(nand1_out | nand2_out);

    // OR gate output
    wire or_out;
    assign or_out = |in;

    // XOR gate output
    wire xor_out;
    assign xor_out = ^in;

    // Assign outputs to module ports
    assign out_nor = nor_out;
    assign out_or = or_out;
    assign out_xor = xor_out;

endmodule