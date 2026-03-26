
module priority_encoder (
    input [7:0] in,
    output reg [2:0] pos
);

always @* begin
    case(in)
        8'b00000001: pos = 3'b000;
        8'b00000010: pos = 3'b001;
        8'b00000100: pos = 3'b010;
        8'b00001000: pos = 3'b011;
        8'b00010000: pos = 3'b100;
        8'b00100000: pos = 3'b101;
        8'b01000000: pos = 3'b110;
        8'b10000000: pos = 3'b111;
        default: pos = 3'b000;
    endcase;
end

endmodule
module barrel_shifter_mux (
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo
);

assign out_hi = in[15:8];
assign out_lo = in[7:0];

endmodule
module top_module (
    input [7:0] in,
    output [2:0] pos,
    input wire [15:0] in2,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo,
    input enable,
    output reg [15:0] out_sum
);

wire [2:0] pos_wire;

priority_encoder pe(
    .in(in),
    .pos(pos_wire)
);

barrel_shifter_mux bsm(
    .in(in2),
    .out_hi(out_hi),
    .out_lo(out_lo)
);

always @(posedge enable) begin
    out_sum <= {pos_wire, 3'b000} + {out_hi, out_lo};
end

assign pos = pos_wire;
endmodule