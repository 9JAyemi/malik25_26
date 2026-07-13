module edge_detector (
    input clk,
    input [15:0] in,
    output reg [15:0] anyedge
);

reg [15:0] prev_in;

always @(posedge clk) begin
    if (in[0] == 1'b0 && prev_in[0] == 1'b1) begin
        anyedge <= in;
    end
    prev_in <= in;
end

endmodule