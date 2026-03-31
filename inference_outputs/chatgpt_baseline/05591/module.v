module barrel_shifter (
    input [15:0] in,
    input [3:0] shift,
    input dir,
    output [15:0] out
);

    wire [15:0] shifted_data_1;
    wire [15:0] shifted_data_2;

    // Pipeline Stage 1
    assign shifted_data_1 = (dir == 0) ? (in << shift) : (in >> shift);

    // Pipeline Stage 2
    assign shifted_data_2 = (dir == 0) ? (shifted_data_1 << shift) : (shifted_data_1 >> shift);

    assign out = shifted_data_2;

endmodule