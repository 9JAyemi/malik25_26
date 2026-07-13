
module mux_encoder_decoder_xor (
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    output [3:0] out
);

    // Priority Encoder
    wire [2:0] encoded_sel;
    priority_encoder pe(sel, encoded_sel);

    // Decoder
    wire [5:0] decoded_sel;
    decoder dec(encoded_sel, decoded_sel);

    // Multiplexer
    wire [3:0] mux_out;
    mux_6to1 mux(
        .sel(encoded_sel[2:0]), // Resized the port to 3 bits
        .data0(data0),
        .data1(data1),
        .data2(data2),
        .data3(data3),
        .data4(data4),
        .data5(data5),
        .out(mux_out)
    );

    // XOR
    wire [3:0] xor_out;
    assign xor_out = mux_out ^ decoded_sel[3:0]; // Resized the port to 3 bits

    // Output
    assign out = xor_out;

endmodule
module priority_encoder (
    input [2:0] in,
    output reg [2:0] out
);

    always @* begin
        case (in)
            3'b000: out = 3'b000;
            3'b001: out = 3'b001;
            3'b010: out = 3'b010;
            3'b011: out = 3'b011;
            3'b100: out = 3'b100;
            3'b101: out = 3'b100;
            3'b110: out = 3'b100;
            3'b111: out = 3'b100;
        endcase
    end

endmodule
module decoder (
    input [2:0] in,
    output reg [5:0] out
);

    always @* begin
        case (in)
            3'b000: out = 6'b000001;
            3'b001: out = 6'b000010;
            3'b010: out = 6'b000100;
            3'b011: out = 6'b001000;
            3'b100: out = 6'b010000;
            3'b101: out = 6'b000000;
            3'b110: out = 6'b000000;
            3'b111: out = 6'b000000;
        endcase
    end

endmodule
module mux_6to1 (
    input [2:0] sel,
    input [3:0] data0,
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    output reg [3:0] out
);

    always @* begin
        case (sel)
            3'b000: out = data0;
            3'b001: out = data1;
            3'b010: out = data2;
            3'b011: out = data3;
            3'b100: out = data4;
            3'b101: out = data5;
            default: out = 4'b0000;
        endcase
    end

endmodule