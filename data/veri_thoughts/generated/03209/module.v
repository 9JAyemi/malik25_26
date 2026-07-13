
module ripple_carry_adder (
    input clk,
    input reset,
    input [3:0] A,
    input [3:0] B,
    output [3:0] OUT
);

reg [3:0] sum;
reg carry;

always @(posedge clk) begin
    if (reset) begin
        sum <= 4'b0;
        carry <= 1'b0;
    end else begin
        {carry, sum} <= A + B + carry;
    end
end

assign OUT = sum;

endmodule
module consecutive_ones_counter (
    input clk,
    input [3:0] in,
    output [3:0] out
);

reg [3:0] counter;

always @(posedge clk) begin
    if (in == 4'b0000) begin
        counter <= 4'b0000;
    end else if (in == 4'b1111) begin
        counter <= 4'b1111;
    end else begin
        counter <= {counter[2:0], in[3]};
    end
end

assign out = counter;

endmodule
module top_module (
    input clk,
    input reset,
    input [3:0] A,
    input [3:0] B,
    output [3:0] OUT,
    output [3:0] counter_out
);

wire [3:0] adder_out;

ripple_carry_adder adder_inst (
    .clk(clk),
    .reset(reset),
    .A(A),
    .B(B),
    .OUT(adder_out)
);

consecutive_ones_counter counter_inst (
    .clk(clk),
    .in(adder_out),
    .out(counter_out)
);

assign OUT = adder_out;

endmodule