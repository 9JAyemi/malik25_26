
module priority_encoder (
    input [7:0] I,
    output reg EN,
    output reg [2:0] Y
);

always @(*) begin
    case (I)
        8'b00000001: begin
            EN = 1'b0;
            Y = 3'b000;
        end
        8'b00000010: begin
            EN = 1'b0;
            Y = 3'b001;
        end
        8'b00000100: begin
            EN = 1'b0;
            Y = 3'b010;
        end
        8'b00001000: begin
            EN = 1'b0;
            Y = 3'b011;
        end
        8'b00010000: begin
            EN = 1'b0;
            Y = 3'b100;
        end
        8'b00100000: begin
            EN = 1'b0;
            Y = 3'b101;
        end
        8'b01000000: begin
            EN = 1'b0;
            Y = 3'b110;
        end
        8'b10000000: begin
            EN = 1'b0;
            Y = 3'b111;
        end
        default: begin
            EN = 1'b1;
            Y = 3'b000;
        end
    endcase
end

endmodule