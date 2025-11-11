
module add16 (
    input [15:0] a,
    input [15:0] b,
    input cin,
    output [15:0] sum,
    output cout
);

    wire [16:0] temp_sum;
    wire carry_out;

    assign {carry_out, temp_sum} = a + b + cin;
    assign sum = {1'b0, temp_sum[15:1]};
    assign cout = carry_out;

endmodule
module top_module (
    input clk,
    input reset,
    input [15:0] in1,
    input [15:0] in2,
    input enable_mult,
    output reg [31:0] out
);

    wire [15:0] adder1_out;
    wire [15:0] adder2_out;
    wire [31:0] mult_out = { {16{1'b0}}, in1 & in2 };

    wire adder1_cout;
    wire adder2_cout;

    add16 adder1(.a(in1), .b(in2), .cin(1'b0), .sum(adder1_out), .cout(adder1_cout));
    add16 adder2(.a(adder1_out), .b(in2), .cin(adder1_cout), .sum(adder2_out), .cout(adder2_cout));

    always @ (posedge clk) begin
        if (reset) begin
            out <= 0;
        end else begin
            if (enable_mult) begin
                out <= mult_out;
            end else begin
                out <= { adder2_out, adder2_cout };
            end
        end
    end

endmodule