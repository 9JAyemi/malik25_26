module priority_encoder (
    input in7,
    input in6,
    input in5,
    input in4,
    input in3,
    input in2,
    input in1,
    input in0,
    output reg out2,
    output reg out1,
    output reg out0
);

always @* begin
    case ({in7, in6, in5, in4, in3, in2, in1, in0})
        8'b00000001, 8'b00000010, 8'b00000100, 8'b00001000, 8'b00010000, 8'b00100000, 8'b01000000, 8'b10000000: begin out2 = 1; out1 = 0; out0 = 0; end
        8'b00000011, 8'b00000101, 8'b00001001, 8'b00010001, 8'b00100001, 8'b01000001, 8'b10000001: begin out2 = 0; out1 = 1; out0 = 0; end
        8'b00000110, 8'b00001010, 8'b00010010, 8'b00100010, 8'b01000010, 8'b10000010: begin out2 = 0; out1 = 0; out0 = 1; end
        default: begin out2 = 0; out1 = 0; out0 = 0; end
    endcase
end

endmodule

module barrel_shifter (
    input [3:0] data,
    input [1:0] shift_amount,
    input mode,
    output reg [3:0] out
);

always @* begin
    case (mode)
        2'b00: out = data << shift_amount;
        2'b01: out = data >> shift_amount;
        default: out = data;
    endcase
end

endmodule

module top_module (
    input clk,
    input reset,
    input [7:0] in,
    input [1:0] shift_amount,
    input mode,
    output reg [7:0] out
);

wire [2:0] priority_encoder_out;
wire [3:0] barrel_shifter_out;
wire [7:0] or_out;

priority_encoder pe(
    .in7(in[7]),
    .in6(in[6]),
    .in5(in[5]),
    .in4(in[4]),
    .in3(in[3]),
    .in2(in[2]),
    .in1(in[1]),
    .in0(in[0]),
    .out2(priority_encoder_out[2]),
    .out1(priority_encoder_out[1]),
    .out0(priority_encoder_out[0])
);

barrel_shifter bs(
    .data(in[3:0]),
    .shift_amount(shift_amount),
    .mode(mode),
    .out(barrel_shifter_out)
);

assign or_out = {priority_encoder_out[2], priority_encoder_out[1], priority_encoder_out[0], barrel_shifter_out};

always @* begin
    out = or_out;
end

endmodule