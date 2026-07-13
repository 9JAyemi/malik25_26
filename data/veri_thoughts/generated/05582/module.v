
module ones_comp (
    input [3:0] binary, // 4-bit input for the ones complement
    output [3:0] out // 4-bit output for the ones complement result
);

    assign out = ~binary; // Compute the ones complement of the input

endmodule

module barrel_shifter (
    input [15:0] DATA, // 16-bit input for the barrel shifter
    input [3:0] SHIFT, // 4-bit input for the shift amount
    input [1:0] CTRL, // 2-bit input for the type of shift
    output [15:0] out // 16-bit output for the shifted result
);

    wire [15:0] temp; // Temporary variable for storing the shifted result
    assign temp = (CTRL == 2'b10) ? {16{DATA[15]}} :  // Handle arithmetic right shift
                 (CTRL == 2'b00) ? DATA :  // Logical left shift
                 (CTRL == 2'b01) ? DATA << SHIFT :  // Logical right shift
                 (CTRL == 2'b11) ? DATA >> SHIFT :  // Rotate right
                 DATA;  // Arithmetic right shift

    assign out = temp;

endmodule

module top_module (
    input [15:0] DATA, // 16-bit input for the barrel shifter
    input [3:0] SHIFT, // 4-bit input for the shift amount
    input [1:0] CTRL, // 2-bit input for the type of shift
    input [3:0] binary, // 4-bit input for the ones complement
    output [15:0] out // 16-bit output for the final result
);

    wire [3:0] ones_comp_out; // Output of the ones complement module
    wire [15:0] shifted_out; // Output of the barrel shifter module

    ones_comp ones_comp_inst (.binary(binary), .out(ones_comp_out)); // Instantiate the ones complement module
    barrel_shifter barrel_shifter_inst (.DATA(DATA), .SHIFT(SHIFT), .CTRL(CTRL), .out(shifted_out)); // Instantiate the barrel shifter module

    assign out = ~shifted_out; // Compute the ones complement of the shifted output

endmodule
