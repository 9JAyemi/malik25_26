module counter (
    input clk,
    input rst,
    input load,
    input [3:0] data_in,
    output reg [3:0] count_out
);

    always @(posedge clk, negedge rst) begin
        if (rst == 0) begin
            count_out <= 4'b0;
        end else if (load == 1) begin
            count_out <= data_in;
        end else begin
            count_out <= count_out + 1;
        end
    end

endmodule