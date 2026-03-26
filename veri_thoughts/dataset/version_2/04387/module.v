module multiplexer_16_to_1 #(parameter BUS_WIDTH = 32)(
    input [BUS_WIDTH-1:0] IN1,
    input [BUS_WIDTH-1:0] IN2,
    input [BUS_WIDTH-1:0] IN3,
    input [BUS_WIDTH-1:0] IN4,
    input [BUS_WIDTH-1:0] IN5,
    input [BUS_WIDTH-1:0] IN6,
    input [BUS_WIDTH-1:0] IN7,
    input [BUS_WIDTH-1:0] IN8,
    input [BUS_WIDTH-1:0] IN9,
    input [BUS_WIDTH-1:0] IN10,
    input [BUS_WIDTH-1:0] IN11,
    input [BUS_WIDTH-1:0] IN12,
    input [BUS_WIDTH-1:0] IN13,
    input [BUS_WIDTH-1:0] IN14,
    input [BUS_WIDTH-1:0] IN15,
    input [BUS_WIDTH-1:0] IN16,
    input [3:0] SELECT,
    output [BUS_WIDTH-1:0] OUT
);

    reg [BUS_WIDTH-1:0] out_reg;

    always @(*) begin
        case (SELECT)
            4'b0000: out_reg = IN1;
            4'b0001: out_reg = IN2;
            4'b0010: out_reg = IN3;
            4'b0011: out_reg = IN4;
            4'b0100: out_reg = IN5;
            4'b0101: out_reg = IN6;
            4'b0110: out_reg = IN7;
            4'b0111: out_reg = IN8;
            4'b1000: out_reg = IN9;
            4'b1001: out_reg = IN10;
            4'b1010: out_reg = IN11;
            4'b1011: out_reg = IN12;
            4'b1100: out_reg = IN13;
            4'b1101: out_reg = IN14;
            4'b1110: out_reg = IN15;
            4'b1111: out_reg = IN16;
        endcase
    end

    assign OUT = out_reg;

endmodule