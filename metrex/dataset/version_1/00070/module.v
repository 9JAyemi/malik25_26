

module ctrl_reg_readback #(parameter CR_WIDTH=6, N_CTRL_REGS=64) (	
	input					clk,
	input					rst,
	input					tx_en,
	input					tx_data_loaded,
	output reg			tx_data_ready,
	output reg			tx_complete,
	output reg [CR_WIDTH-1:0]  tx_cnt
);

always @(posedge clk) begin
	if (rst) begin
		tx_cnt <= 0;
		tx_data_ready <= 0;
		tx_complete <= 0;
	end else begin
		if (!tx_complete && tx_en) begin if (tx_data_ready && tx_data_loaded) begin tx_data_ready <= 0;
				if (tx_cnt == N_CTRL_REGS-1) begin tx_complete <= 1; 
					tx_cnt <= tx_cnt;
					end
				else begin
					tx_complete <= tx_complete;
					tx_cnt <= tx_cnt + 1;
					end
				end
			else begin
				tx_complete <= tx_complete;
				tx_cnt <= tx_cnt;
				tx_data_ready <= (!tx_data_ready && !tx_data_loaded) ? 1 : tx_data_ready; end
		end else if (tx_complete && !tx_en) begin tx_cnt <= 0;
			tx_data_ready <= 0;
			tx_complete <= 0;
		end else begin
			tx_data_ready <= tx_data_ready;
			tx_complete <= tx_complete;
			tx_cnt <= tx_cnt;
		end
	end end endmodule
