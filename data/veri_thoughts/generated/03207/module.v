module adder_barrelshifter (
    input wire [15:0] in1,
    input wire [15:0] in2,
    input wire [3:0] shift_amt,
    input wire shift_dir, // 0 for right shift, 1 for left shift
    output wire [15:0] out
);

    wire [15:0] adder_out;
    wire [15:0] shifted_out;

    // 16-bit adder
    assign adder_out = in1 + in2;

    // Barrel shifter
    assign shifted_out = (shift_dir == 1) ? (adder_out << shift_amt) : (adder_out >> shift_amt);

    // Output
    assign out = shifted_out;

endmodule

module top_module (
    input wire [15:0] in1,
    input wire [15:0] in2,
    input wire [3:0] shift_amt,
    input wire shift_dir, // 0 for right shift, 1 for left shift
    output wire [15:0] out
);

    adder_barrelshifter ab (
        .in1(in1),
        .in2(in2),
        .shift_amt(shift_amt),
        .shift_dir(shift_dir),
        .out(out)
    );

endmodule