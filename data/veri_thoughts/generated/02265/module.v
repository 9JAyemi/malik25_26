module clock_divider(
    input clk_in,
    output reg clk_out_1,
    output reg clk_out_2,
    output reg clk_out_3
);

reg [25:0] counter_25;
reg [26:0] counter_12_5;
reg [27:0] counter_6_25;

always @(posedge clk_in) begin
    counter_25 <= counter_25 + 1;
    counter_12_5 <= counter_12_5 + 1;
    counter_6_25 <= counter_6_25 + 1;
    
    if (counter_25 == 999_999) begin
        counter_25 <= 0;
        clk_out_1 <= ~clk_out_1;
    end
    
    if (counter_12_5 == 1_999_999) begin
        counter_12_5 <= 0;
        clk_out_2 <= ~clk_out_2;
    end
    
    if (counter_6_25 == 3_999_999) begin
        counter_6_25 <= 0;
        clk_out_3 <= ~clk_out_3;
    end
end

endmodule