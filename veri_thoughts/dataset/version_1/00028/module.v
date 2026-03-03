module top_module (
    input CLK,
    input UP_DOWN,
    input RESET,
    input EN,
    input select,
    input [3:0] A,
    input [3:0] B,
    output [3:0] OUT1,
    output [7:0] OUT2
);

wire [3:0] counter_out;
wire [7:0] multiplier_out;

up_down_counter udc (
    .CLK(CLK),
    .UP_DOWN(UP_DOWN),
    .RESET(RESET),
    .EN(EN),
    .OUT(counter_out)
);

binary_multiplier bm (
    .A(select ? A : B),
    .B(select ? B : A),
    .OUT(multiplier_out)
);

assign OUT1 = counter_out;
assign OUT2 = multiplier_out;

endmodule

module up_down_counter (
    input CLK,
    input UP_DOWN,
    input RESET,
    input EN,
    output [3:0] OUT
);

reg [3:0] count;

always @(posedge CLK or posedge RESET) begin
    if (RESET) begin
        count <= 4'b0;
    end else if (EN) begin
        count <= UP_DOWN ? count + 4'b1 : count - 4'b1;
    end
end

assign OUT = count;

endmodule

module binary_multiplier (
    input [3:0] A,
    input [3:0] B,
    output [7:0] OUT
);

assign OUT = A * B;

endmodule