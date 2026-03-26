module half_adder
(
    input       x_in,       // one bit input data
    input       y_in,       // one bit input data
    output      s_out,      // sum of two input
    output      c_out       // carry of two input
);

assign s_out = x_in ^ y_in;
assign c_out = x_in & y_in;

endmodule

module full_adder
(
    input       x_in,       // one bit input data
    input       y_in,       // one bit input data
    input       c_in,       // one bit carry data
    output      wire s_out, // sum of two input
    output      wire c_out  // carry of two input
);

wire wire_sum0;
wire wire_carry0;
wire wire_carry1;

half_adder U0_half_adder (
    .x_in(x_in),
    .y_in(y_in),
    .s_out(wire_sum0),
    .c_out(wire_carry0)
);

half_adder U1_half_adder (
    .x_in(wire_sum0),
    .y_in(c_in),
    .s_out(s_out),
    .c_out(wire_carry1)
);

assign c_out = wire_carry0 | wire_carry1;

endmodule
