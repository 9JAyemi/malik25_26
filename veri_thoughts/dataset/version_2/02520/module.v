
module edge_detection (
    input clk,
    input [7:0] in,
    output reg [7:0] out
);
    reg [7:0] prev_in;
    
    always @(posedge clk) begin
        if (in != prev_in) begin
            out <= {1'b0, in[7:1]};
        end else begin
            out <= {1'b0, 7'b0};
        end
        prev_in <= in;
    end
endmodule
