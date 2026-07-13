module top_module(
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo,
    output wire [8:0] out_parity,
    output wire [7:0] out_or
);

    wire [7:0] lo_byte;
    wire [7:0] hi_byte;
    wire [8:0] parity_byte;
    wire [7:0] complement_lo_byte;

    // Instantiate modified half-word splitter module
    half_word_splitter_mod splitter(
        .in(in),
        .out_hi(hi_byte),
        .out_lo(lo_byte)
    );

    // Instantiate modified odd parity generator module
    odd_parity_generator_mod parity_generator(
        .in(lo_byte),
        .out(parity_byte)
    );

    // Compute complement of the lower byte output from the parity generator module
    assign complement_lo_byte = ~parity_byte[7:0];

    // XOR the complement of the lower byte output with the upper byte output from the splitter module
    wire [7:0] xor1_output;
    assign xor1_output = hi_byte ^ complement_lo_byte;

    // XOR the output of the first XOR gate with the original upper byte output from the splitter module
    assign out_or = xor1_output ^ hi_byte;

    // Output the upper and lower bytes and the parity byte
    assign out_hi = hi_byte;
    assign out_lo = lo_byte;
    assign out_parity = parity_byte;

endmodule

// Modified half-word splitter module
module half_word_splitter_mod(
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo
);

    assign out_hi = in[15:8];
    assign out_lo = in[7:0];

endmodule

// Modified odd parity generator module
module odd_parity_generator_mod(
    input wire [7:0] in,
    output wire [8:0] out
);

    assign out[7:0] = in;
    assign out[8] = ^in;

endmodule