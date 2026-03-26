module up_down_counter (
    input clk,
    input reset,
    input up_down,
    output reg [2:0] count
);

    always @(posedge clk or negedge reset) begin
        if (!reset) begin
            count <= 3'b0;
        end else begin
            if (up_down) begin
                count <= count + 1;
            end else begin
                count <= count - 1;
            end
        end
    end

endmodule