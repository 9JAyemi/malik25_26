module top_module (
    input [3:0] A,
    input [3:0] B,
    input clk,
    input reset,
    input enable,
    output reg [7:0] result
);

    wire [7:0] mult_out;
    wire [3:0] count_out;

    multiplier mult_inst (
        .A(A),
        .B(B),
        .result(mult_out)
    );

    counter count_inst (
        .clk(clk),
        .reset(reset),
        .enable(enable),
        .count(count_out)
    );

    always @(*) begin
        result = mult_out + count_out;
    end

endmodule

module multiplier (
    input [3:0] A,
    input [3:0] B,
    output reg [7:0] result
);

    always @(*) begin
        result = A * B;
    end

endmodule

module counter (
    input clk,
    input reset,
    input enable,
    output reg [3:0] count
);

    always @(posedge clk) begin
        if (reset) begin
            count <= 0;
        end else if (enable) begin
            count <= count + 1;
        end
    end

endmodule