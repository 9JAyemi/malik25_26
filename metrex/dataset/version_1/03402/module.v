module counter (
    input clk,
    input [3:0] reset,
    input [3:0] load,
    input [3:0] increment,
    output reg [3:0] count
);

always @(posedge clk) begin
    if (reset == 4'b1111) begin
        count <= 4'b0000;
    end else if (load != 4'b0000) begin
        count <= load;
    end else begin
        count <= count + increment;
    end
end

endmodule