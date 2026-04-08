
module counter_module (
    input clk,
    input reset,
    output [7:0] count
);

parameter max_count = 255;
reg [7:0] internal_count;

always @(posedge clk or posedge reset) begin
    if (reset) begin
        internal_count <= 8'd0;
    end else if (internal_count == max_count) begin
        internal_count <= 8'd0;
    end else begin
        internal_count <= internal_count + 1;
    end
end

assign count = internal_count;

endmodule
