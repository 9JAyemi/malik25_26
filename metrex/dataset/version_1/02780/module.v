
module top_module (
    input [3:0] in,
    input [3:0] A,
    input [3:0] B,
    output [5:0] final_output
); 

wire [1:0] priority_output;
wire [3:0] ripple_sum;
wire carry;

priority_encoder pe(
    .in(in),
    .out(priority_output)
);

ripple_carry_adder rca(
    .A(A),
    .B(B),
    .SUM(ripple_sum),
    .CARRY(carry)
);

functional_module fm(
    .priority_output(priority_output),
    .ripple_sum(ripple_sum),
    .final_output(final_output)
);

endmodule

module priority_encoder (
    input [3:0] in,
    output [1:0] out
);
assign out = (in == 4'b0001) ? 2'b00 :
              (in == 4'b0010) ? 2'b01 :
              (in == 4'b0100) ? 2'b10 :
              (in == 4'b1000) ? 2'b11 : 2'b11;
endmodule

module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    output [3:0] SUM,
    output CARRY
);
assign {CARRY, SUM} = A + B;
endmodule

module functional_module (
    input [1:0] priority_output,
    input [3:0] ripple_sum,
    output [5:0] final_output
);
assign final_output = {priority_output, ripple_sum};
endmodule
