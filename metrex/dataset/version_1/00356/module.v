
module bitwise_and_func (
    input wire [7:0] vec1,
    input wire [7:0] vec2,
    input wire select,
    output wire [7:0] and_out,
    output wire [15:0] sum_out
);

    // Bitwise AND module
    assign and_out = (select) ? 8'b0 : vec1 & vec2;

    // Functional module
    assign sum_out = vec1 + vec2;

endmodule
module top_module ( 
    input wire [7:0] vec1,
    input wire [7:0] vec2,
    output wire [7:0] outv,
    output wire [15:0] sum
);

    bitwise_and_func baf (
        .vec1(vec1),
        .vec2(vec2),
        .select(1'b0),
        .and_out(outv),
        .sum_out(sum)
    );

endmodule