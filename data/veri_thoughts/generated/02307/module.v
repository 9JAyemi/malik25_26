module edge_detector (
    input clk,
    input [7:0] in,
    output reg [7:0] anyedge
);

reg [7:0] prev_in;

always @(posedge clk) begin
    if (in != prev_in) begin
        anyedge <= 8'b00000001;
    end else begin
        anyedge <= 8'b00000000;
    end
    prev_in <= in;
end

endmodule

module top_module (
    input clk,
    input [7:0] in,
    output [7:0] anyedge
);

edge_detector detector (
    .clk(clk),
    .in(in),
    .anyedge(anyedge)
);

endmodule