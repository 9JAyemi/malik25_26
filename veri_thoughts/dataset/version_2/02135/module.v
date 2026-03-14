module binary_counter(
    input clk, rst,
    output reg [3:0] count,
    output reg max
    );
    
    always @(posedge clk) begin
        if (rst) begin
            count <= 0;
            max <= 0;
        end
        else begin
            if (count == 4'b1011) begin
                count <= 0;
                max <= 1;
            end
            else begin
                count <= count + 1;
                max <= 0;
            end
        end
    end
endmodule