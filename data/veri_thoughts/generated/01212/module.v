module dec_table(
    input [2:0] address,  // 3-bit address for 8 possible entries
    input clock,
    output reg [15:0] q   // 16-bit wide output data
);

    always @(posedge clock) begin
        case (address)
            3'b000: q <= 16'h0001; // Map address 0 to value 0001
            3'b001: q <= 16'h0002; // Map address 1 to value 0002
            3'b010: q <= 16'h0004; // Map address 2 to value 0004
            3'b011: q <= 16'h0008; // Map address 3 to value 0008
            3'b100: q <= 16'h0010; // Map address 4 to value 0010
            3'b101: q <= 16'h0020; // Map address 5 to value 0020
            3'b110: q <= 16'h0040; // Map address 6 to value 0040
            3'b111: q <= 16'h0080; // Map address 7 to value 0080
            default: q <= 16'h0000; // Default case (should never happen with 3-bit address)
        endcase
    end

endmodule
