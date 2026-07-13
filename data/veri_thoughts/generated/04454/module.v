module decoder_2to4(
    input A,
    input B,
    input enable,
    output reg [3:0] out
);

always @(*) begin
    if (enable) begin
        case ({A, B})
            2'b00: out = 4'b0000;
            2'b01: out = 4'b0100;
            2'b10: out = 4'b0110;
            2'b11: out = 4'b0111;
        endcase
    end else begin
        out = 4'b0000;
    end
end

endmodule