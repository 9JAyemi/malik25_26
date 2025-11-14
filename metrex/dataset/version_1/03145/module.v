module top_module ( 
    input [2:0] sel, 
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    input select, // Select input to choose between priority encoder and decoder
    output reg [3:0] out   );

    wire [5:0] enc_out;
    wire [7:0] dec_out;
    wire [3:0] mux_out;

    priority_encoder pe (
        .in({data0[3], data1[3], data2[3], data3[3], data4[3], data5[3]}),
        .out(enc_out)
    );

    decoder dec (
        .in(sel),
        .out(dec_out)
    );

    assign mux_out = select ? dec_out[sel*4 +: 4] : data0[sel] ? data0 : data1[sel] ? data1 : data2[sel] ? data2 : data3[sel] ? data3 : data4[sel] ? data4 : data5;

    always @(*) begin
        out = mux_out;
    end

endmodule

module priority_encoder (
    input [5:0] in,
    output reg [5:0] out
);

    always @(*) begin
        casez(in)
            6'b100000: out = 6'b000001;
            6'b010000: out = 6'b000010;
            6'b001000: out = 6'b000100;
            6'b000100: out = 6'b001000;
            6'b000010: out = 6'b010000;
            6'b000001: out = 6'b100000;
            default: out = 6'b000000;
        endcase
    end

endmodule

module decoder (
    input [2:0] in,
    output reg [7:0] out
);

    always @(*) begin
        case(in)
            3'b000: out = 8'b00000001;
            3'b001: out = 8'b00000010;
            3'b010: out = 8'b00000100;
            3'b011: out = 8'b00001000;
            3'b100: out = 8'b00010000;
            3'b101: out = 8'b00100000;
            3'b110: out = 8'b01000000;
            3'b111: out = 8'b10000000;
            default: out = 8'b00000000;
        endcase
    end

endmodule