module binary_counter(
    input clk,
    input reset,
    output reg [3:0] count
);

    always @(posedge clk) begin
        if (reset) begin
            count <= 4'd0;
        end
        else begin
            if (count == 4'd15) begin
                count <= 4'd0;
            end
            else begin
                count <= count + 4'd1;
            end
        end
    end

endmodule