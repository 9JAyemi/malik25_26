module bcd_converter (
    input [3:0] binary,
    output reg [3:0] bcd_high,
    output reg [3:0] bcd_low
);

always @* begin
    case (binary)
        4'b0000: begin bcd_high = 4'b0000; bcd_low = 4'b0000; end
        4'b0001: begin bcd_high = 4'b0000; bcd_low = 4'b0001; end
        4'b0010: begin bcd_high = 4'b0000; bcd_low = 4'b0010; end
        4'b0011: begin bcd_high = 4'b0000; bcd_low = 4'b0011; end
        4'b0100: begin bcd_high = 4'b0000; bcd_low = 4'b0100; end
        4'b0101: begin bcd_high = 4'b0000; bcd_low = 4'b0101; end
        4'b0110: begin bcd_high = 4'b0000; bcd_low = 4'b0110; end
        4'b0111: begin bcd_high = 4'b0000; bcd_low = 4'b0111; end
        4'b1000: begin bcd_high = 4'b0001; bcd_low = 4'b0000; end
        4'b1001: begin bcd_high = 4'b0001; bcd_low = 4'b0001; end
        4'b1010: begin bcd_high = 4'b0001; bcd_low = 4'b0010; end
        4'b1011: begin bcd_high = 4'b0001; bcd_low = 4'b0011; end
        4'b1100: begin bcd_high = 4'b0001; bcd_low = 4'b0100; end
        4'b1101: begin bcd_high = 4'b0001; bcd_low = 4'b0101; end
        4'b1110: begin bcd_high = 4'b0001; bcd_low = 4'b0110; end
        4'b1111: begin bcd_high = 4'b0001; bcd_low = 4'b0111; end
        default: begin bcd_high = 4'b0000; bcd_low = 4'b0000; end
    endcase
end

endmodule

module absolute_value (
    input [3:0] binary,
    output reg [3:0] abs_val
);

always @* begin
    if (binary[3] == 1) begin
        abs_val = ~binary + 1;
    end else begin
        abs_val = binary;
    end
end

endmodule

module abs_bcd_converter (
    input [3:0] binary,
    output reg [3:0] bcd_high,
    output reg [3:0] bcd_low,
    output reg [3:0] abs_val,
    output reg [11:0] abs_bcd_val
);

bcd_converter bcd_converter_inst (
    .binary(binary),
    .bcd_high(bcd_high),
    .bcd_low(bcd_low)
);

absolute_value absolute_value_inst (
    .binary(binary),
    .abs_val(abs_val)
);

always @* begin
    if (abs_val[3] == 1) begin
        abs_bcd_val = {4'b0001, ~bcd_high + 1, ~bcd_low + 1};
    end else begin
        abs_bcd_val = {4'b0000, bcd_high, bcd_low};
    end
end

endmodule

module top_module (
    input clk,
    input reset,
    input [3:0] binary,
    output [3:0] bcd_high,
    output [3:0] bcd_low,
    output reg [3:0] abs_val,
    output reg [11:0] abs_bcd_val
);

abs_bcd_converter abs_bcd_converter_inst (
    .binary(binary),
    .bcd_high(bcd_high),
    .bcd_low(bcd_low),
    .abs_val(abs_val),
    .abs_bcd_val(abs_bcd_val)
);

endmodule