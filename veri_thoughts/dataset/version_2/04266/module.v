module binary_counter(
    input reset,
    input enable,
    input clk,
    output reg [3:0] count
);

    always @(posedge clk) begin
        if (reset) begin
            count <= 0;
        end else if (enable) begin
            if (count == 15) begin
                count <= 0;
            end else begin
                count <= count + 1;
            end
        end
    end

endmodule