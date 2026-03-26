module binary_counter (
    output reg [3:0] count,
    input clk,
    input rst
);

    always @(posedge clk) begin
        if (rst) begin
            count <= 4'b0000;
        end
        else begin
            count <= count + 1;
        end
    end

endmodule