
module four_bit_comparator (
    input [3:0] A,
    input [3:0] B,
    output wire EQ,
    output wire GT,
    output wire LT
);
    assign EQ = (A == B);
    assign GT = (A > B);
    assign LT = (A < B);
endmodule

module four_bit_shift_register (
    input clk,
    input reset,
    input serial_in,
    input shift,
    output reg [3:0] parallel_out
);
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            parallel_out <= 4'b0000;
        end else if (shift) begin
            parallel_out <= {serial_in, parallel_out[3:1]};
        end
    end
endmodule

module functional_module (
    input EQ,
    input GT,
    input LT,
    input [3:0] parallel_out,
    output reg final_output
);
    always @(*) begin
        if ((EQ || GT || LT) && (parallel_out != 4'b0000)) begin
            final_output = 1;
        end else begin
            final_output = 0;
        end
    end
endmodule

module top_module (
    input clk,
    input reset,
    input [3:0] A,
    input [3:0] B,
    input serial_in,
    input shift,
    output [3:0] parallel_out,
    output final_output
);
    wire EQ, GT, LT;

    four_bit_comparator comparator (
        .A(A),
        .B(B),
        .EQ(EQ),
        .GT(GT),
        .LT(LT)
    );

    four_bit_shift_register shift_register (
        .clk(clk),
        .reset(reset),
        .serial_in(serial_in),
        .shift(shift),
        .parallel_out(parallel_out)
    );

    functional_module func_module (
        .EQ(EQ),
        .GT(GT),
        .LT(LT),
        .parallel_out(parallel_out),
        .final_output(final_output)
    );
endmodule
