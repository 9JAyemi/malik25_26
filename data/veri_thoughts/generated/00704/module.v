module register (
    input clk,
    input rst,
    input [7:0] data_in,
    input enable,
    output reg [7:0] data_out
);

reg [7:0] stored_data;

always @(posedge clk) begin
    if (rst) begin
        stored_data <= 8'h00;
    end else if (enable) begin
        stored_data <= data_in;
    end
end

always @*
    data_out = stored_data;

endmodule