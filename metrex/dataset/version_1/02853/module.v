module counter #(
    parameter WIDTH = 8
)(
    input clk,
    input rst,
    input enable,
    input [WIDTH-1:0] mod,
    output reg [WIDTH-1:0] count,
    output reg done
);

always @(posedge clk) begin
    if (rst) begin
        count <= 0;
        done <= 0;
    end else if (enable) begin
        if (count == mod-1) begin
            count <= 0;
            done <= 1;
        end else begin
            count <= count + 1;
            done <= 0;
        end
    end
end

endmodule