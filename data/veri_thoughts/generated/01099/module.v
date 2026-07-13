module priority_encoder_and_ripple_carry_adder (
    input [3:0] I,
    input [3:0] A,
    input [3:0] B,
    input Cin,
    input select,
    output reg [1:0] Y,
    output reg [3:0] Sum
);

wire [1:0] priority_enc_out;
wire [3:0] ripple_carry_out;

priority_encoder priority_enc_inst (
    .I(I),
    .Y(priority_enc_out)
);

ripple_carry_adder ripple_carry_inst (
    .A(A),
    .B(B),
    .Cin(Cin),
    .Sum(ripple_carry_out)
);

always @(*) begin
    if (select == 0) begin
        Y <= priority_enc_out;
        Sum <= 4'b0;
    end else begin
        Y <= 2'b0;
        Sum <= ripple_carry_out;
    end
end

endmodule

module priority_encoder (
    input [3:0] I,
    output reg [1:0] Y
);

always @* begin
    case (I)
        4'b0001: Y = 2'b00;
        4'b0010: Y = 2'b01;
        4'b0100: Y = 2'b10;
        4'b1000: Y = 2'b11;
        default: Y = 2'b00;
    endcase
end

endmodule

module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    input Cin,
    output reg [3:0] Sum
);

reg [3:0] temp;

always @* begin
    temp = A + B + Cin;
    Sum = temp[3:0];
end

endmodule