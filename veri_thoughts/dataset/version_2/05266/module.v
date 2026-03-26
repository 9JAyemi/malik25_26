module top_module (
    input [7:0] a, b, c, d,
    output [7:0] max);

    wire [7:0] ab_max, cd_max, abcd_max;

    // Compare a and b
    comparator cmp_ab(a, b, ab_max);

    // Compare c and d
    comparator cmp_cd(c, d, cd_max);

    // Compare ab_max and cd_max
    comparator cmp_abcd(ab_max, cd_max, abcd_max);

    assign max = abcd_max;

endmodule

module comparator (
    input [7:0] a, b,
    output reg [7:0] max);

    always @(*) begin
        if (a > b) begin
            max = a;
        end else begin
            max = b;
        end
    end

endmodule