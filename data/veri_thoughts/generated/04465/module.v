
module data_path(
    input [15:0] in_data,
    input in_valid,
    input out_ready,
    output reg [15:0] out_data,
    output reg out_valid,
    output reg out_error,
	input clk
);

wire [1:0] error_type;
assign error_type = 2'b00; // no errors

always @ (posedge clk) begin
    if (in_valid) begin
        if (out_ready) begin
            out_data <= in_data;
            out_valid <= 1'b1;
            out_error <= 1'b0;
        end else begin
            out_data <= 16'h0000;
            out_valid <= 1'b0;
            out_error <= 1'b1;
        end
    end else begin
        out_data <= 16'h0000;
        out_valid <= 1'b0;
        out_error <= 1'b0;
    end
end

endmodule