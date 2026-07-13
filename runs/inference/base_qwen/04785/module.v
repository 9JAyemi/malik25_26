module decimal_to_binary(
    input [3:0] in_value,
    output reg [3:0] out_value
);

    always @(*) begin
        case (in_value)
            4'b0000: out_value = 4'b0000;
            4'b0001: out_value = 4'b0001;
            4'b0010: out_value = 4'b0010;
            4'b0011: out_value = 4'b0011;
            4'b0100: out_value = 4'b0100;
            4'b0101: out_value = 4'b0101;
            4'b0110: out_value = 4'b0110;
            4'b0111: out_value = 4'b0111;
            4'b1000: out_value = 4'b1000;
            4'b1001: out_value = 4'b1001;
            default: out_value = 4'bXXXX;
        endcase
    end
endmodule