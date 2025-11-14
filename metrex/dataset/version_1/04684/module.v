
module top_module (
    input clk,
    input reset,
    input [7:0] d1,
    input [7:0] d2,
    input [3:0] adder_input,
    output [3:0] final_output
);

// Corrected the declaration of shift_register_output to be a wire.
wire [7:0] shift_register_output;
wire [3:0] ripple_carry_adder_output;

shift_register shift_reg (
    .clk(clk),
    .reset(reset),
    .d(d1),
    .q(shift_register_output)
);

ripple_carry_adder ripple_adder (
    .a(shift_register_output[3:0]),
    .b(adder_input),
    .sum(ripple_carry_adder_output),
    .carry_out()
);

functional_module func_mod (
    .shift_register_output(shift_register_output),
    .ripple_carry_adder_output(ripple_carry_adder_output),
    .final_output(final_output)
);

// Corrected the declaration of shift_register_output2 to be a wire.
wire [7:0] shift_register_output2;
shift_register shift_reg2 (
    .clk(clk),
    .reset(reset),
    .d(d2),
    .q(shift_register_output2)
);

endmodule

module shift_register (
    input clk,
    input reset,
    input [7:0] d,
    output reg [7:0] q
);

always @(posedge clk, posedge reset) begin
    if (reset) begin
        q <= 8'b0;
    end else begin
        q <= {q[6:0], d[0]};
    end
end

endmodule

module ripple_carry_adder(
    input [3:0] a,
    input [3:0] b,
    output [3:0] sum,
    output carry_out
);

assign {carry_out, sum} = a + b;

endmodule

module functional_module (
    input [7:0] shift_register_output,
    input [3:0] ripple_carry_adder_output,
    output [3:0] final_output
);

assign final_output = shift_register_output[7:4] + ripple_carry_adder_output;

endmodule
