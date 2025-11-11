
module min_module (
    input [7:0] a, b, c, d, // Inputs to find minimum
    output reg [7:0] min // Output minimum value
);

reg [7:0] ab_min, cd_min, abcd_min;

always @(*) begin
    ab_min = (a < b) ? a : b;
    cd_min = (c < d) ? c : d;
    abcd_min = (ab_min < cd_min) ? ab_min : cd_min;
    min = abcd_min;
end

endmodule

module add_module (
    input [7:0] x, y, // Inputs to add
    output [7:0] sum, // Output sum
    output overflow // Output overflow
);

wire [8:0] x_plus_y, x_minus_y, y_minus_x; // Use wider wires to prevent overflow

assign x_plus_y = x + y;
assign x_minus_y = x - y;
assign y_minus_x = y - x;

assign sum = x_plus_y[7:0]; // Truncate to 8 bits to match input/output width

assign overflow = x_plus_y[8] ^ x[7] ^ y[7]; // XOR of MSBs indicates overflow

endmodule

module top_module (
    input [7:0] a, b, c, d, // Inputs to the minimum module
    input [7:0] x, y, // Inputs to the addition module
    input select, // Selects which module to use as input to the functional module
    output [7:0] result, // Output of the functional module
    output overflow // Output of the addition module indicating overflow
);

wire [7:0] min_output, add_output; // Wire to connect outputs of min and add modules

min_module min_inst (
    .a(a),
    .b(b),
    .c(c),
    .d(d),
    .min(min_output)
);

add_module add_inst (
    .x(x),
    .y(y),
    .sum(add_output),
    .overflow(overflow)
);

assign result = select ? min_output : add_output; // Select output based on 'select' input

endmodule
