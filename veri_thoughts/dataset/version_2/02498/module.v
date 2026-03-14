
module top_module (
    input [3:0] in,
    output reg [7:0] out
);

reg [3:0] twos_comp_out;
reg [3:0] bcd_out;

twos_complement twos_comp_inst (
    .in(in),
    .out(twos_comp_out)
);

bcd_converter bcd_inst (
    .binary_input(in),
    .bcd_output(bcd_out)
);

output_combiner combiner_inst (
    .twos_comp_input(twos_comp_out),
    .bcd_input(bcd_out),
    .combined_output(out)
);

endmodule
module twos_complement (
    input [3:0] in,
    output reg [3:0] out
);

always @ (*) begin
    out = (~in) + 1;
end

endmodule
module bcd_converter (
    input [3:0] binary_input,
    output reg [3:0] bcd_output
);

always @ (*) begin
    case (binary_input)
        4'b0000: bcd_output = 4'b0000;
        4'b0001: bcd_output = 4'b0001;
        4'b0010: bcd_output = 4'b0010;
        4'b0011: bcd_output = 4'b0011;
        4'b0100: bcd_output = 4'b0100;
        4'b0101: bcd_output = 4'b0101;
        4'b0110: bcd_output = 4'b0110;
        4'b0111: bcd_output = 4'b0111;
        4'b1000: bcd_output = 4'b1000;
        4'b1001: bcd_output = 4'b1001;
        4'b1010: bcd_output = 4'b0001;
        4'b1011: bcd_output = 4'b0010;
        4'b1100: bcd_output = 4'b0011;
        4'b1101: bcd_output = 4'b0100;
        4'b1110: bcd_output = 4'b0101;
        4'b1111: bcd_output = 4'b0110;
    endcase
end

endmodule
module output_combiner (
    input [3:0] twos_comp_input,
    input [3:0] bcd_input,
    output reg [7:0] combined_output
);

always @ (*) begin
    combined_output = {twos_comp_input, bcd_input};
end

endmodule