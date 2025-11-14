
module counter(
    input clk,
    input reset,
    output reg [3:0] count,
    output reg control
);

always @(posedge clk) begin
    if (reset == 1) begin
        count <= 4'b0000;
        control <= 1'b0;
    end
    else begin
        if (count == 4'b1111) begin
            count <= 4'b0000;
        end
        else begin
            count <= count + 1;
        end
        
        if (count[0] == 1) begin
            control <= 1'b1;
        end
        else begin
            control <= 1'b0;
        end
    end
end

endmodule