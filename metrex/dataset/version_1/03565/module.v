
module shift_adder (
    input CLK,
    input RST,
    input LD,
    input [3:0] D,
    input [15:0] A,
    input [15:0] B,
    output [15:0] SUM
);

wire [3:0] shift_reg;
wire [15:0] signed_sum;

// Shift register module
shift_reg_mod shift_reg_inst (
    .CLK(CLK),
    .RST(RST),
    .LD(LD),
    .D(D),
    .OUT(shift_reg)
);

// Signed magnitude adder module
signed_adder signed_adder_inst (
    .A(A),
    .B(B),
    .SUM(signed_sum)
);

// Functional module that adds the output of shift register and signed magnitude adder
assign SUM = shift_reg + signed_sum;

endmodule
module shift_reg_mod (
    input CLK,
    input RST,
    input LD,
    input [3:0] D,
    output reg [3:0] OUT
);

always @(posedge CLK) begin
    if (RST) begin
        OUT <= 4'b0;
    end else if (LD) begin
        OUT <= D;
    end else begin
        OUT <= {OUT[2:0], 1'b0};
    end
end

endmodule
module signed_adder (
    input [15:0] A,
    input [15:0] B,
    output reg [15:0] SUM
);

wire [15:0] abs_A;
wire [15:0] abs_B;
wire [15:0] signed_sum;

assign abs_A = (A[15]) ? ~A + 1 : A;
assign abs_B = (B[15]) ? ~B + 1 : B;

assign signed_sum = (A[15] == B[15]) ? {A[15], abs_A + abs_B} :
                    (abs_A > abs_B) ? {A[15], abs_A - abs_B} :
                    {B[15], abs_B - abs_A};

always @(signed_sum) begin
    SUM <= signed_sum;
end

endmodule