module four_to_two(
    input [3:0] in_data,
    output reg [1:0] out_data
);

always @(*) begin
    case(in_data)
        4'b0000: out_data = 2'b00;
        4'b0001: out_data = 2'b01;
        4'b0010: out_data = 2'b10;
        4'b0011: out_data = 2'b11;
        default: out_data = 2'b00;
    endcase
end

endmodule