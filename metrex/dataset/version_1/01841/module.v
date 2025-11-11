
module half_adder (
    input x_in,
    input y_in,
    output wire s_out,
    output wire c_out
);

assign s_out = x_in ^ y_in;
assign c_out = x_in & y_in;

endmodule
module full_adder (
    input A,
    input B,
    input C_in,
    output reg S,
    output reg C_out
);

wire S1, C1, C2;

half_adder HA1(.x_in(A), .y_in(B), .s_out(S1), .c_out(C1));
half_adder HA2(.x_in(S1), .y_in(C_in), .s_out(S), .c_out(C2));

always @(*) begin
    C_out <= C1 | C2;
end

endmodule