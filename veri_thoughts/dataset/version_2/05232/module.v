module up_counter_with_comparator (
    input clk,
    input slowena,
    input reset,
    input [3:0] threshold,
    output [3:0] count,
    output high_if_count_greater_than_threshold
);

    reg [3:0] count_reg;
    wire count_greater_than_threshold;

    assign high_if_count_greater_than_threshold = count_greater_than_threshold;
    assign count = count_reg;

    always @(posedge clk) begin
        if (reset) begin
            count_reg <= 4'b0000;
        end else if (slowena) begin
            count_reg <= count_reg + 1;
        end
    end

    assign count_greater_than_threshold = (count_reg >= threshold);

endmodule

module top_module (
    input clk,
    input slowena,
    input reset,
    input [3:0] threshold,
    output [3:0] count,
    output high_if_count_greater_than_threshold
);

    up_counter_with_comparator counter (
        .clk(clk),
        .slowena(slowena),
        .reset(reset),
        .threshold(threshold),
        .count(count),
        .high_if_count_greater_than_threshold(high_if_count_greater_than_threshold)
    );

endmodule