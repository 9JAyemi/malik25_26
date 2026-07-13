
module ripple_carry_adder (
    input [3:0] A,
    input [3:0] B,
    output [3:0] S,
    output C
);

    assign {C, S} = A + B;

endmodule
module shift_register (
    input clk,
    input [3:0] din,
    input load,
    input shift,
    output reg [3:0] dout
);

    always @(posedge clk) begin
        if (load) begin
            dout <= din;
        end else if (shift) begin
            dout <= {dout[2:0], 1'b0};
        end
    end

endmodule
module top_module (
    input clk,
    input reset, // Synchronous active-high reset
    input select, // Select input to choose between adder and shift_register
    input [3:0] A, // 4-bit input for the adder
    input [3:0] B, // 4-bit input for the adder
    input [3:0] din, // 4-bit input for the shift_register
    input load, // Load input for the shift_register
    input shift, // Shift input for the shift_register
    output [7:0] out // 8-bit output from the active module
);

    wire [3:0] S;
    wire C;
    wire [3:0] dout;

    ripple_carry_adder adder_inst (
        .A(A),
        .B(B),
        .S(S),
        .C(C)
    );

    shift_register shift_reg_inst (
        .clk(clk),
        .din(din),
        .load(load),
        .shift(shift),
        .dout(dout)
    );

    assign out = {S, dout};

endmodule