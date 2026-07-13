
module counter (
    input clk,
    input reset,
    input [3:0] N,
    output reg [3:0] count_out
);

    always @(posedge clk, posedge reset) begin
        if (reset) begin
            count_out <= 4'b0000;
        end else if (count_out == N) begin
            count_out <= 4'b0000;
        end else begin
            count_out <= count_out + 1;
        end
    end

endmodule
module adder_subtractor (
    input [3:0] A,
    input [3:0] B,
    input mode,
    output reg [3:0] out
);

    always @(*) begin
        if (mode) begin
            out = A + B;
        end else begin
            out = A - B;
        end
    end

endmodule
module top_module (
    input clk,
    input reset,
    input [3:0] N,
    input [3:0] B,
    input mode,
    input select,
    output reg [3:0] q
);

    wire [3:0] count_out;
    wire [3:0] out;

    counter counter_inst (
        .clk(clk),
        .reset(reset),
        .N(N),
        .count_out(count_out)
    );

    adder_subtractor adder_subtractor_inst (
        .A(count_out),
        .B(B),
        .mode(mode),
        .out(out)
    );

    always @(posedge clk) begin
        if (select) begin
            q <= count_out;
        end else begin
            q <= out;
        end
    end

endmodule