module binary_to_bcd_converter (
    input [3:0] binary_in,
    output reg [3:0] bcd_out,
    output reg greater_than_nine
);
    
    always @(*) begin
        case (binary_in)
            4'b0000: bcd_out = 4'b0000;
            4'b0001: bcd_out = 4'b0001;
            4'b0010: bcd_out = 4'b0010;
            4'b0011: bcd_out = 4'b0011;
            4'b0100: bcd_out = 4'b0100;
            4'b0101: bcd_out = 4'b0101;
            4'b0110: bcd_out = 4'b0110;
            4'b0111: bcd_out = 4'b0111;
            4'b1000: bcd_out = 4'b1000;
            4'b1001: bcd_out = 4'b0001;
            4'b1010: bcd_out = 4'b0010;
            4'b1011: bcd_out = 4'b0011;
            4'b1100: bcd_out = 4'b0100;
            4'b1101: bcd_out = 4'b0101;
            4'b1110: bcd_out = 4'b0110;
            4'b1111: bcd_out = 4'b0111;
            default: bcd_out = 4'bxxxx;
        endcase
        
        if (binary_in > 4'b1001) begin
            greater_than_nine = 1;
        end
        else begin
            greater_than_nine = 0;
        end
    end
    
endmodule