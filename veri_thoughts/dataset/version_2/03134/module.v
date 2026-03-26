module up_down_counter (
    input clk,
    input rst,
    input dir,
    output reg [3:0] count
);

    always @(posedge clk or negedge rst) begin
        if (!rst) begin
            count <= 4'b0;
        end
        else begin
            if (dir) begin
                count <= count + 1;
            end
            else begin
                count <= count - 1;
            end
        end
    end

endmodule