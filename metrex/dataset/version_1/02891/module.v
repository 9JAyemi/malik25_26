
module expand_message (
	input clk,
	input [56-1:0] rx_fixed_data,
	input [59:0] rx_nonce,
	output reg [511:0] tx_expanded_message
);

	parameter IDX_0 = 56'd0;
	parameter IDX_1 = 56'd1;
	parameter IDX_2 = 56'd2;
	parameter IDX_3 = 56'd3;
	parameter IDX_4 = 56'd4;
	parameter IDX_5 = 56'd5;
	parameter IDX_6 = 56'd6;

	parameter IDX4_0 = 60'd0;
	parameter IDX4_1 = 60'd1;
	parameter IDX4_2 = 60'd2;
	parameter IDX4_3 = 60'd3;
	parameter IDX4_4 = 60'd4;
	parameter IDX4_5 = 60'd5;
	parameter IDX4_6 = 60'd6;
	parameter IDX4_7 = 60'd7;
	parameter IDX4_8 = 60'd8;
	parameter IDX4_9 = 60'd9;
	parameter IDX4_10 = 60'd10;
	parameter IDX4_11 = 60'd11;
	parameter IDX4_12 = 60'd12;
	parameter IDX4_13 = 60'd13;
	parameter IDX4_14 = 60'd14;

	always @ (posedge clk)
	begin
		tx_expanded_message <= {32'd192, 32'h0, 224'h0, 32'h80000000, rx_fixed_data[IDX_2], rx_fixed_data[IDX_1], rx_fixed_data[IDX_0], 8'h00, rx_fixed_data[IDX_6], rx_fixed_data[IDX_5], rx_fixed_data[IDX_4], rx_fixed_data[IDX_3], {4'b0,rx_nonce[IDX4_2]}, {4'b0,rx_nonce[IDX4_1]}, {4'b0,rx_nonce[IDX4_0]}, 8'h00, {4'b0,rx_nonce[IDX4_6]}, {4'b0,rx_nonce[IDX4_5]}, {4'b0,rx_nonce[IDX4_4]}, {4'b0,rx_nonce[IDX4_3]}, {4'b0,rx_nonce[IDX4_10]}, {4'b0,rx_nonce[IDX4_9]}, {4'b0,rx_nonce[IDX4_8]}, {4'b0,rx_nonce[IDX4_7]}, {4'b0,rx_nonce[IDX4_14]}, {4'b0,rx_nonce[IDX4_13]}, {4'b0,rx_nonce[IDX4_12]}, {4'b0,rx_nonce[IDX4_11]}};
	end

endmodule