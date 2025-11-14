module binary_to_onehot (
    input [2:0] B,
    output reg [7:0] Y
);

always @(*) begin
    case(B)
        3'b000: Y = 8'b00000001;
        3'b001: Y = 8'b00000010;
        3'b010: Y = 8'b00000100;
        3'b011: Y = 8'b00001000;
        3'b100: Y = 8'b00010000;
        3'b101: Y = 8'b00100000;
        3'b110: Y = 8'b01000000;
        3'b111: Y = 8'b10000000;
    endcase
end

endmodule

module up_down_counter (
    input clk,
    input reset,
    input Up,
    input Down,
    input Load,
    input [7:0] D,
    output reg [7:0] Q
);

reg [7:0] next_Q;

always @(posedge clk) begin
    if(reset) begin
        Q <= 8'b00000000;
    end else if(Load) begin
        Q <= D;
    end else if(Up) begin
        next_Q = Q + 1;
        Q <= next_Q;
    end else if(Down) begin
        next_Q = Q - 1;
        Q <= next_Q;
    end
end

endmodule

module one_hot_counter (
    input clk,
    input reset,
    input [2:0] B,
    input Up,
    input Down,
    input Load,
    output reg [7:0] Q
);

wire [7:0] onehot;
wire [7:0] next_onehot;

binary_to_onehot converter(
    .B(B),
    .Y(onehot)
);

up_down_counter counter(
    .clk(clk),
    .reset(reset),
    .Up(Up),
    .Down(Down),
    .Load(Load),
    .D(onehot),
    .Q(next_onehot)
);

always @(posedge clk) begin
    if(reset) begin
        Q <= 8'b00000000;
    end else begin
        Q <= next_onehot;
    end
end

endmodule

module top_module (
    input clk,
    input reset,
    input [2:0] B,
    input Up,
    input Down,
    input Load,
    output reg [7:0] Q
);

one_hot_counter counter(
    .clk(clk),
    .reset(reset),
    .B(B),
    .Up(Up),
    .Down(Down),
    .Load(Load),
    .Q(Q)
);

endmodule