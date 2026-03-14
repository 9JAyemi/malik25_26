
module up_down_counter (
    input clk,
    input up_down,
    input [3:0] load,
    output [7:0] count
);

reg [7:0] count;

always @(posedge clk) begin
    if (load != 0) begin
        count <= load;
    end else if (up_down == 1) begin
        count <= count + 1;
    end else begin
        count <= count - 1;
    end
end

endmodule