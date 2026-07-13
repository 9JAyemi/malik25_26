
module up_down_counter (
    input clk,
    input areset,
    input load,
    input up_down,
    input count_enable,
    output reg [3:0] count_out
);

always @(posedge clk or negedge areset) begin
    if (areset == 0) begin
        count_out <= 4'b0000;
    end else if (load == 1) begin
        count_out <= 4'b0000;
    end else if (count_enable == 1) begin
        if (up_down == 1) begin
            count_out <= count_out + 1;
        end else begin
            count_out <= count_out - 1;
        end
    end
end

endmodule
