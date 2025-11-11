module binary_counter(
    input clk,
    input rst,
    input en,
    input ctrl,
    output reg [3:0] count
);

always @(posedge clk) begin
    if (rst) begin
        count <= 4'b0;
    end else if (en) begin
        if (ctrl) begin
            count <= count - 1;
        end else begin
            count <= count + 1;
        end
    end
end

endmodule