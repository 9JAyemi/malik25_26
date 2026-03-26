
module little_endian_counter (
    input clk,
    input [3:0] data_in,
    output reg [3:0] data_out
);

    always @(posedge clk) begin
        if (data_in == 4'b1111) begin
            data_out <= 4'b0000;
        end else begin
            data_out <= data_in + 1;
        end
    end

endmodule