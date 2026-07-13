module addr_decode(
    input [3:0] addr,
    output reg r,
    output reg s,
    output reg t,
    output reg x,
    output reg y,
    output reg z
);

    always @(*) begin
        case(addr)
            4'b0001, 4'b0010: r = 1;
            default: r = 0;
        endcase
        
        case(addr)
            4'b0011, 4'b0100: s = 1;
            default: s = 0;
        endcase
        
        case(addr)
            4'b0101, 4'b0110: t = 1;
            default: t = 0;
        endcase
        
        case(addr)
            4'b1000, 4'b1001: x = 1;
            default: x = 0;
        endcase
        
        case(addr)
            4'b1010, 4'b1011: y = 1;
            default: y = 0;
        endcase
        
        case(addr)
            4'b1100, 4'b1111: z = 1;
            default: z = 0;
        endcase
    end

endmodule