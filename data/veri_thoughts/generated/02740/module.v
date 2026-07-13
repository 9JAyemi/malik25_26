
module shift_register (
    input clk,
    input reset,            // Synchronous active-high reset
    input [7:0] in,         // 8-bit input
    output [7:0] out,       // 8-bit output for the final output
    output [7:0] reg_out    // 8-bit output for the shifted register
);

reg [7:0] shift_reg;

barrel_shifter bs (
    .in(in),
    .out(reg_out)
);

always @(posedge clk) begin
    if (reset) begin
        shift_reg <= 8'b0;
    end else begin
        shift_reg <= reg_out;
    end
end

xor_gate xg (
    .in1(in),
    .in2(shift_reg),
    .out(out)
);

endmodule
module barrel_shifter (
    input [7:0] in,         // 8-bit input
    output [7:0] out        // 8-bit output for the shifted output
);

assign out = {in[6:0], 1'b0};

endmodule
module xor_gate (
    input [7:0] in1,        // 8-bit input from the shift register
    input [7:0] in2,        // 8-bit input from the input port
    output [7:0] out        // 8-bit output (XOR of the two inputs)
);

assign out = in1 ^ in2;

endmodule