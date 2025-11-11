
module up_down_counter (
    input clk,
    input up_down,
    output reg [3:0] count
);
    always @(posedge clk) begin
        if (up_down) begin
            count <= count + 1;
        end else begin
            count <= count - 1;
        end
    end
endmodule
module binary_adder (
    input [3:0] A,
    input [3:0] B,
    output [3:0] sum
);
    assign sum = A + B;
endmodule
module shift_and_sum (
    input [3:0] A,
    input [3:0] B,
    input clk,
    input up_down,
    output [7:0] out
);
    wire [3:0] counter1_out;
    wire [3:0] counter2_out;
    wire [3:0] binary_adder_out;

    up_down_counter counter1 (.clk(clk), .up_down(up_down), .count(counter1_out));
    up_down_counter counter2 (.clk(clk), .up_down(up_down), .count(counter2_out));

    binary_adder adder (.A(counter1_out), .B(counter2_out), .sum(binary_adder_out));

    assign out = {A >> B, binary_adder_out};
endmodule