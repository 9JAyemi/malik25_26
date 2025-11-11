module priority_encoder (
    input [3:0] binary_in, // 4-bit binary input
    output reg [1:0] priority_out // 2-bit priority output
);

always @* begin
    casez(binary_in)
        4'b0001: priority_out = 2'b00;
        4'b0010: priority_out = 2'b01;
        4'b0100: priority_out = 2'b10;
        4'b1000: priority_out = 2'b11;
        default: priority_out = 2'b00;
    endcase
end

endmodule

module gray_code_generator (
    input [3:0] priority_in, // 4-bit input for priority encoder
    output [3:0] gray_code // 4-bit Gray code sequence output
);

wire [1:0] priority_out;
priority_encoder pe(priority_in, priority_out);

assign gray_code[0] = priority_out[0] ^ priority_out[1];
assign gray_code[1] = priority_out[0];
assign gray_code[2] = priority_out[1];
assign gray_code[3] = gray_code[2] ^ gray_code[1];

endmodule