
module top_module(
    input wire clk,
    input wire [7:0] in,
    output reg [7:0] out
);

    wire [2:0] pos;
    wire [7:0] out_hi, out_lo;
    reg select; // Declare 'select' as a reg

    priority_encoder pe(
        .in(in),
        .pos(pos)
    );

    word_splitter ws(
        .in({8'b0, in}),  // Pad 8 zeros to input to match port width
        .out_hi(out_hi),
        .out_lo(out_lo)
    );

    always @(*) begin  // Use a combinational always block for select
        select = (pos == 0) ? 1'b0 : 1'b1;
    end

    always @(posedge clk) begin
        if (select) begin
            out <= out_hi; // Use blocking assignment '=<' for registers
        end else begin
            out <= out_lo; // Use blocking assignment '=<' for registers
        end
    end

endmodule

module priority_encoder (
    input [7:0] in,
    output reg [2:0] pos
);

    always @(*) begin
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
        endcase
    end

endmodule

module word_splitter (
    input wire [15:0] in,
    output reg [7:0] out_hi,
    output reg [7:0] out_lo
);

    always @(*) begin
        out_hi = in >> 8;
        out_lo = in & 8'hFF;
    end

endmodule
