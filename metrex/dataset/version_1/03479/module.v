module my_module (
    input clk,
    input rst,
    input [15:0] data_in,
    output reg [15:0] data_out,
    output reg valid
);

reg [15:0] prev_data_in;

always @(posedge clk) begin
    if (rst) begin
        data_out <= 16'h0000;
        valid <= 1'b0;
        prev_data_in <= data_in;
    end
    else if (data_in !== prev_data_in) begin
        data_out <= ~data_in;
        valid <= 1'b1;
        prev_data_in <= data_in;
    end
    else begin
        data_out <= data_out;
        valid <= valid;
    end
end

endmodule