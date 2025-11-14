
module top_module (
    input wire [31:0] in,
    input clk,
    input reset,      // Synchronous active-high reset
    output [3:0] q,
    output wire [7:0] sum_out
);

    wire [7:0] byte1, byte4;
    wire [3:0] count_out;
    wire [7:0] load_value;

    // Extract the 1st and 4th bytes from the input word
    assign byte1 = in[7:0];
    assign byte4 = in[31:24];

    // Swap the two bytes
    assign load_value = {byte4, in[23:8], in[15:8], byte1};

    // Instantiate the 4-bit binary counter
    counter_4bit counter(
        .clk(clk),
        .reset(reset),
        .load(load_value),
        .q(q)
    );

    // Instantiate the additional functional module to calculate the sum
    sum_module sum(
        .a(count_out),
        .b(load_value),
        .sum_out(sum_out)
    );

    // Assign the output of the counter to the input of the sum module
    assign count_out = q;

endmodule

module counter_4bit (
    input clk,
    input reset,
    input [7:0] load,
    output reg [3:0] q
);

    always @(posedge clk) begin
        if (reset) begin
            q <= 4'b0000;
        end else if (load != q) begin
            q <= load[3:0];
        end else begin
            q <= q + 1;
        end
    end

endmodule

module sum_module (
    input [3:0] a,
    input [7:0] b,
    output wire [7:0] sum_out
);

    assign sum_out = a + b;

endmodule
