module top_module (
    input clk,
    input reset,
    input enable,
    input [15:0] A,
    input [15:0] B,
    output [3:0] counter_out,
    output [15:0] adder_sum,
    output overflow,
    output [15:0] final_output
);

    // Instantiate counter module
    counter_4bit counter_inst (
        .clk(clk),
        .reset(reset),
        .enable(enable),
        .out(counter_out)
    );

    // Instantiate ripple carry adder module
    ripple_carry_adder adder_inst (
        .A(A),
        .B(B),
        .sum(adder_sum),
        .overflow(overflow)
    );

    // Functional module to compute final output
    assign final_output = (counter_out > adder_sum) ? counter_out : adder_sum;

endmodule

// 4-bit counter module
module counter_4bit (
    input clk,
    input reset,
    input enable,
    output reg [3:0] out
);

    always @(posedge clk) begin
        if (reset) begin
            out <= 4'b0;
        end else if (enable) begin
            out <= out + 1;
        end
    end

endmodule

// Ripple carry adder module
module ripple_carry_adder (
    input [15:0] A,
    input [15:0] B,
    output reg [15:0] sum,
    output overflow
);

    assign overflow = (A[15] & B[15] & ~sum[15]) | (~A[15] & ~B[15] & sum[15]);

    always @(A, B) begin
        sum = A + B;
    end

endmodule