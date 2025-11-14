module top_module (
    input clk,
    input reset,
    input [7:0] in1,
    input [7:0] in2,
    input select,
    output reg [7:0] out
);

    wire [7:0] sum;
    wire [7:0] diff;

    adder add_inst (
        .a(in1),
        .b(in2),
        .sum(sum)
    );

    subtractor sub_inst (
        .a(in1),
        .b(in2),
        .diff(diff)
    );

    always @ (posedge clk) begin
        if (reset) begin
            out <= 8'b0;
        end else begin
            if (select) begin
                out <= diff;
            end else begin
                out <= sum;
            end
        end
    end

endmodule

module adder (
    input [7:0] a,
    input [7:0] b,
    output [7:0] sum
);

    assign sum = a + b;

endmodule

module subtractor (
    input [7:0] a,
    input [7:0] b,
    output [7:0] diff
);

    assign diff = a - b;

endmodule