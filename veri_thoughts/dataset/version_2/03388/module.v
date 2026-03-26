module counter (
    input clk,
    input rst,
    output reg [2:0] count
);

always @ (posedge clk or posedge rst) begin
    if (rst) begin
        count <= 0;
    end else begin
        if (count == 7) begin
            count <= 0;
        end else begin
            count <= count + 1;
        end
    end
end

endmodule