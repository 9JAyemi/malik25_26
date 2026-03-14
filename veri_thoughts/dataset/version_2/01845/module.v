module binary_counter(
    input clk,
    input rst,
    output reg [1:0] count,
    output reg overflow
);

    always @(posedge clk or negedge rst) begin
        if(rst == 0) begin
            count <= 2'b00;
            overflow <= 0;
        end
        else begin
            if(count == 2'b11) begin
                count <= 2'b00;
                overflow <= 1;
            end
            else begin
                count <= count + 1;
                overflow <= 0;
            end
        end
    end

endmodule