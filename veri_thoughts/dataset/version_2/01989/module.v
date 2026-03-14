
module shift_adder (
    input CLK,
    input LOAD,
    input SHIFT,
    input [7:0] DATA_IN,
    output [7:0] Q_OUT,
    output [7:0] Q_BAR_OUT
);

reg [7:0] shift_reg;
wire [3:0] constant = 4'b1111;

assign Q_OUT = shift_reg;
assign Q_BAR_OUT = ~shift_reg;

always @(posedge CLK) begin
    if (LOAD) begin
        shift_reg <= DATA_IN;
    end else if (SHIFT) begin
        shift_reg <= {DATA_IN[7], shift_reg[7:1]};
    end
end

wire [7:0] sum;
adder add_inst (
    .A(shift_reg),
    .B(constant),
    .C(sum)
);

endmodule
module adder (
    input [7:0] A,
    input [3:0] B,
    output [7:0] C
);

assign C = A + B;

endmodule