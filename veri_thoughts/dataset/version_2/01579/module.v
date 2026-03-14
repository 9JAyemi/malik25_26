module simple_counter(
    input clk,
    input reset,
    output reg [7:0] count
);

always @(posedge clk) begin
    if (reset) begin
        count <= 8'h00;
    end else begin
        if (count == 8'hFF) begin
            count <= 8'h00;
        end else begin
            count <= count + 1;
        end
    end
end

endmodule