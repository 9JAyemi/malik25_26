module counter_4bit(
    input clk,
    input reset,
    output reg [3:0] count,
    output reg max_count
);

always @(posedge clk or negedge reset) begin
    if (reset == 0) begin
        count <= 0;
        max_count <= 0;
    end else begin
        if (count == 4'hF) begin
            count <= 0;
            max_count <= 1;
        end else begin
            count <= count + 1;
            max_count <= 0;
        end
    end
end

endmodule