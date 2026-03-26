module binary_to_gray(
    input clk,
    input rst,
    input [31:0] data_in,
    output reg [7:0] data_out
);

reg [7:0] gray_latch;

always @(posedge clk) begin
    if (rst) begin
        gray_latch <= 8'b00000000;
    end else begin
        gray_latch <= {1'b0, data_in[7], data_in[7]^data_in[6], data_in[6]^data_in[5], data_in[5]^data_in[4], data_in[4]^data_in[3], data_in[3]^data_in[2], data_in[2]^data_in[1], data_in[1]^data_in[0]};
    end
end

always @(*) begin
    data_out = gray_latch;
end

endmodule