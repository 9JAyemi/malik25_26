module counter
(
    input wire clk,
    input wire rst,
    input wire load,
    input wire [3:0] init,
    output reg [3:0] out
);

    always @ (posedge clk) begin
        if (rst) begin
            out <= 4'b0;
        end
        else if (load) begin
            out <= init;
        end
        else begin
            out <= (out == 4'b1111) ? 4'b0 : out + 1;
        end
    end
    
endmodule