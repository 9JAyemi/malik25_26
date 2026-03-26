
module xor_concat_adder(
    input wire [7:0] in_hi,
    input wire [7:0] in_lo,
    output wire [15:0] final_output
);

    // Define the internal wires
    wire [15:0] concat_output;
    wire xor_output;

    // Instantiate the concatenation module
    concat_16bit concat_16(.in_hi(in_hi), .in_lo(in_lo), .out(concat_output));

    // Instantiate the XOR gate
    xor_gate xor_1(.in1(in_hi[0]), .in2(in_lo[0]), .out(xor_output));
    
    assign final_output = {xor_output, concat_output[15:8]};

endmodule
module concat_16bit(
    input wire [7:0] in_hi,
    input wire [7:0] in_lo,
    output wire [15:0] out
);

    assign out = {in_hi, in_lo};

endmodule
module xor_gate(
    input wire in1,
    input wire in2,
    output wire out
);

    assign out = in1 ^ in2;

endmodule