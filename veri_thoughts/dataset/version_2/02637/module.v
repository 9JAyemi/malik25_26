
module barrel_shifter (
    input [3:0] A,
    input [1:0] B,
    output reg [3:0] Q
);

always @(*) begin
    case(B)
        2'b00: Q = A;
        2'b01: Q = {A[0], A[3:1]};
        2'b10: Q = {A[1:0], A[3:2]};
        2'b11: Q = {A[2:0], A[3]};
    endcase
end

endmodule
module up_counter (
    input clk,
    input reset,
    output reg [3:0] Q
);

always @(posedge clk) begin
    if (reset) begin
        Q <= 4'b0000;
    end else begin
        Q <= Q + 1;
        if (Q == 4'b1111) begin
            Q <= 4'b0000;
        end
    end
end

endmodule
module adder (
    input [3:0] A,
    input [3:0] B,
    output [7:0] Q
);

assign Q = A + B;

endmodule
module top_module (
    input clk,
    input reset,
    input [3:0] A,
    input [1:0] B,
    output [7:0] Q
);

wire [3:0] shifted_counter;
wire [3:0] counter;
wire [3:0] shifted_value;
wire [3:0] zero = 4'b0000;

barrel_shifter shifter(
    .A(counter),
    .B(B),
    .Q(shifted_counter)
);

up_counter counter_inst(
    .clk(clk),
    .reset(reset),
    .Q(counter)
);

barrel_shifter shifter2(
    .A(zero),
    .B(B),
    .Q(shifted_value)
);

adder adder_inst(
    .A(shifted_counter),
    .B(shifted_value),
    .Q(Q)
);

endmodule