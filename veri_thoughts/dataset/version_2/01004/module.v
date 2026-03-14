module binary_to_bcd_converter (
    input [2:0] binary_in,
    output reg [3:0] bcd_out
);

always @(*) begin
    case (binary_in)
        3'b000: bcd_out = 4'b0000;
        3'b001: bcd_out = 4'b0001;
        3'b010: bcd_out = 4'b0010;
        3'b011: bcd_out = 4'b0011;
        3'b100: bcd_out = 4'b0100;
        3'b101: bcd_out = 4'b0101;
        3'b110: bcd_out = 4'b0110;
        3'b111: bcd_out = 4'b0111;
    endcase;
end

endmodule

module priority_multiplexer (
    input [3:0] in0,
    input [7:0] in1,
    input P,
    output reg [7:0] out
);

always @(*) begin
    if (P) begin
        out = in1;
    end else begin
        out = in0;
    end
end

endmodule

module bcd_adder (
    input [3:0] bcd_in,
    input [7:0] c_in,
    input clk,
    input reset,       // Synchronous active-high reset
    output reg [7:0] q
);

always @(posedge clk or negedge reset) begin
    if (!reset) begin
        q <= 8'b00000000;
    end else begin
        q <= bcd_in + c_in;
    end
end

endmodule

module top_module (
    input clk,
    input reset,       // Synchronous active-high reset
    input [2:0] D,     // 3-bit binary input for the binary-to-BCD converter
    input S,           // Select input for choosing between BCD digits and C
    input P,           // Priority input for choosing C over BCD digits
    input [7:0] C,     // Input for the priority multiplexer
    output [7:0] q     // 8-bit output from the functional module
);

wire [3:0] bcd_out;
wire [7:0] c_out;
binary_to_bcd_converter bcd_converter(.binary_in(D), .bcd_out(bcd_out));
priority_multiplexer priority_mux(.in0(bcd_out), .in1(C), .P(P), .out(c_out));
bcd_adder adder(.bcd_in(bcd_out), .c_in(c_out), .clk(clk), .reset(reset), .q(q));

endmodule