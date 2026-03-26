
module top_module (
    input [3:0] in,
    input S,
    input P,
    output reg Y
);

    wire [15:0] decoder_out;
    wire mux_out;

    decoder_4to16 decoder_inst (
        .in(in),
        .out(decoder_out)
    );

    priority_mux mux_inst (
        .A(decoder_out[S]),
        .B(decoder_out[S+1]),
        .C(in[2]),
        .S(S),
        .P(P),
        .Y(mux_out)
    );

    always @(*) begin
        if (P) begin
            Y = in[2];
        end else begin
            Y = mux_out;
        end
    end

endmodule

module decoder_4to16 (
    input [3:0] in,
    output reg [15:0] out
);

    always @(*) begin
        case (in)
            4'b0000: out = 16'b0000000000000001;
            4'b0001: out = 16'b0000000000000010;
            4'b0010: out = 16'b0000000000000100;
            4'b0011: out = 16'b0000000000001000;
            4'b0100: out = 16'b0000000000010000;
            4'b0101: out = 16'b0000000000100000;
            4'b0110: out = 16'b0000000001000000;
            4'b0111: out = 16'b0000000010000000;
            4'b1000: out = 16'b0000000100000000;
            4'b1001: out = 16'b0000001000000000;
            4'b1010: out = 16'b0000010000000000;
            4'b1011: out = 16'b0000100000000000;
            4'b1100: out = 16'b0001000000000000;
            4'b1101: out = 16'b0010000000000000;
            4'b1110: out = 16'b0100000000000000;
            4'b1111: out = 16'b1000000000000000;
        endcase
    end

endmodule

module priority_mux (
    input A,
    input B,
    input C,
    input S,
    input P,
    output reg Y
);

    always @(*) begin
        if (P) begin
            Y = C;
        end else begin
            if (S) begin
                Y = A;
            end else begin
                Y = B;
            end
        end
    end

endmodule
