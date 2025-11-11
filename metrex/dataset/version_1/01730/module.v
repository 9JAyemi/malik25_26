module min_finder (
    input [7:0] a, b, c, d,
    output [7:0] min);

    wire [7:0] ab_min, cd_min;
    wire [7:0] abcd_min;

    // Find minimum of a and b
    pipeline_stage #(.WIDTH(8)) stage1 (.in_a(a), .in_b(b), .out(ab_min));

    // Find minimum of c and d
    pipeline_stage #(.WIDTH(8)) stage2 (.in_a(c), .in_b(d), .out(cd_min));

    // Find minimum of ab_min and cd_min
    pipeline_stage #(.WIDTH(8)) stage3 (.in_a(ab_min), .in_b(cd_min), .out(abcd_min));

    assign min = abcd_min;

endmodule

module pipeline_stage #(
    parameter WIDTH = 8
) (
    input [WIDTH-1:0] in_a,
    input [WIDTH-1:0] in_b,
    output reg [WIDTH-1:0] out
);

    always @(*) begin
        if (in_a < in_b) begin
            out = in_a;
        end else begin
            out = in_b;
        end
    end

endmodule