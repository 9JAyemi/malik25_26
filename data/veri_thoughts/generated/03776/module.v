
module binary_squarer (
    input [3:0] binary,
    output reg [7:0] square
);

always @(*) begin
    square = binary * binary;
end

endmodule
module ring_counter (
    input clk,
    input reset,
    output reg [3:0] count
);

always @(posedge clk) begin
    if (reset) begin
        count <= 4'b0000;
    end else begin
        count <= {count[2:0], count[3]};
    end
end

endmodule
module summing_module (
    input [7:0] square,
    input [3:0] count,
    output reg [3:0] sum
);

always @(*) begin
    sum = square[7:4] + count;
end

endmodule
module top_module (
    input clk,
    input reset,
    input [3:0] binary,
    output reg [3:0] bit_0,
    output reg [3:0] bit_1,
    output reg [3:0] bit_2,
    output reg [3:0] bit_3,
    output reg [3:0] sum
);

wire [7:0] square;

binary_squarer bs(
    .binary(binary),
    .square(square)
);

wire [3:0] count;

ring_counter rc(
    .clk(clk),
    .reset(reset),
    .count(count)
);

summing_module sm(
    .square(square),
    .count(count),
    .sum(sum)
);

always @(*) begin
    bit_0 = square[3:0];
    bit_1 = square[7:4];
    bit_2 = count;
    bit_3 = sum;
end

endmodule