module barrel_shifter (
    input [3:0] A,
    input [1:0] B,
    output [3:0] Q,
    output COUT
);

wire [3:0] shifted_value;
assign shifted_value = (B[1]) ? {A[3], A[3:1]} : (B[0]) ? {A[2:0], A[3]} : A;

assign Q = shifted_value;
assign COUT = shifted_value[0] & (B[1] | B[0]);

endmodule

module up_down_counter (
    input clk,
    input reset,
    input up_down,
    output reg [3:0] count
);

always @(posedge clk) begin
    if (reset) begin
        count <= 4'b0;
    end else if (up_down) begin
        count <= count + 1;
    end else begin
        count <= count - 1;
    end
end

endmodule

module functional_module (
    input [3:0] barrel_shifted_value,
    input [3:0] counter_value,
    output [7:0] sum
);

assign sum = {barrel_shifted_value, counter_value};

endmodule

module top_module (
    input clk,
    input reset,
    input up_down,
    input [3:0] A,
    input [1:0] B,
    output [3:0] Q,
    output COUT,
    output [3:0] count,
    output [7:0] sum
);

barrel_shifter bs (
    .A(A),
    .B(B),
    .Q(Q),
    .COUT(COUT)
);

up_down_counter udc (
    .clk(clk),
    .reset(reset),
    .up_down(up_down),
    .count(count)
);

functional_module fm (
    .barrel_shifted_value(Q),
    .counter_value(count),
    .sum(sum)
);

endmodule