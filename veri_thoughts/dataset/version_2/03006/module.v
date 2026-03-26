module priority_encoder (
    input [3:0] in,
    output reg [1:0] pos
);

reg [3:0] temp;

always @* begin
    if (in[3] == 1) temp = 3;
    else if (in[2] == 1) temp = 2;
    else if (in[1] == 1) temp = 1;
    else if (in[0] == 1) temp = 0;
    else temp = 4'b0000;
end

always @* begin
    case (temp)
        4'b0001: pos = 2'b00;
        4'b0010: pos = 2'b01;
        4'b0100: pos = 2'b10;
        4'b1000: pos = 2'b11;
        default: pos = 2'b00;
    endcase
end

endmodule