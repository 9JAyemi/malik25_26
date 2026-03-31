
module functional_module (
    input [3:0] B, // 4-bit binary input for binary-to-excess-3 converter
    input [1:0] in, // 2-bit input for decoder
    output reg [15:0] out // 16-bit output with only one bit set to 1
);

    wire [3:0] E;
    wire [15:0] D;
    
    binary_to_excess_3 BtoE (
        .B(B), 
        .E(E)
    );
    
    decoder dec (
        .in(in),
        .out(D)
    );
    
    always @* begin
        // Update the out register based on D and E
        out <= D << E;
    end

endmodule
module binary_to_excess_3(
    input [3:0] B,
    output reg [3:0] E
);

always @* begin
    case(B)
        4'b0000:      E = 4'b0011;
        4'b0001:      E = 4'b0100;
        4'b0010:      E = 4'b0101;
        4'b0011:      E = 4'b0110;
        4'b0100:      E = 4'b0111;
        4'b0101:      E = 4'b1000;
        4'b0110:      E = 4'b1001;
        4'b0111:      E = 4'b1010;
        4'b1000:      E = 4'b1011;
        4'b1001:      E = 4'b1100;
        4'b1010:      E = 4'b1101;
        4'b1011:      E = 4'b1110;
        4'b1100:      E = 4'b1111;
        4'b1101:      E = 4'b0001;
        4'b1110:      E = 4'b0010;
        4'b1111:      E = 4'b0011;
    endcase
end
endmodule
module decoder(
    input [1:0] in,
    output reg [15:0] out
);

always @* begin
    case(in)
        2'b00:      out = 16'b0000000000000001;
        2'b01:      out = 16'b0000000000000010;
        2'b10:      out = 16'b0000000000000100;
        2'b11:      out = 16'b0000000000001000;
    endcase
end
endmodule