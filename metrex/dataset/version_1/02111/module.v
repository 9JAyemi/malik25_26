


module pcie_fc_cntl 
(
input									pcie_user_clk,
	input									pcie_user_rst_n,

input	[11:0]							fc_cpld,
	input	[7:0]							fc_cplh,
	input	[11:0]							fc_npd,
	input	[7:0]							fc_nph,
	input	[11:0]							fc_pd,
	input	[7:0]							fc_ph,
	output	[2:0]							fc_sel,

	input									tx_cfg_req,
	output									tx_cfg_gnt,
	input	[5:0]							tx_buf_av,

	output									tx_cpld_gnt,
	output									tx_mrd_gnt,
	output									tx_mwr_gnt
);

parameter	P_RX_CONSTRAINT_FC_CPLD		= 32;
parameter	P_RX_CONSTRAINT_FC_CPLH		= 8;

parameter	P_TX_CONSTRAINT_FC_CPLD		= 1;
parameter	P_TX_CONSTRAINT_FC_CPLH		= 1;
parameter	P_TX_CONSTRAINT_FC_NPD		= 1;
parameter	P_TX_CONSTRAINT_FC_NPH		= 1;
parameter	P_TX_CONSTRAINT_FC_PD		= 32;
parameter	P_TX_CONSTRAINT_FC_PH		= 1;

localparam	S_RX_AVAILABLE_FC_SEL			= 2'b01;
localparam	S_TX_AVAILABLE_FC_SEL			= 2'b10;

reg		[1:0]								cur_state;
reg		[1:0]								next_state;

reg		[11:0]							r_rx_available_fc_cpld;
reg		[7:0]							r_rx_available_fc_cplh;
reg		[11:0]							r_rx_available_fc_npd;
reg		[7:0]							r_rx_available_fc_nph;
reg		[11:0]							r_rx_available_fc_pd;
reg		[7:0]							r_rx_available_fc_ph;

reg		[11:0]							r_tx_available_fc_cpld;
reg		[7:0]							r_tx_available_fc_cplh;
reg		[11:0]							r_tx_available_fc_npd;
reg		[7:0]							r_tx_available_fc_nph;
reg		[11:0]							r_tx_available_fc_pd;
reg		[7:0]							r_tx_available_fc_ph;

wire									w_rx_available_fc_cpld;
wire									w_rx_available_fc_cplh;

wire									w_tx_available_fc_cpld;
wire									w_tx_available_fc_cplh;
wire									w_tx_available_fc_npd;
wire									w_tx_available_fc_nph;
wire									w_tx_available_fc_pd;
wire									w_tx_available_fc_ph;

reg		[2:0]							r_fc_sel;
reg		[1:0]							r_rd_fc_sel;
reg		[1:0]							r_rd_fc_sel_d1;
reg		[1:0]							r_rd_fc_sel_d2;

reg										r_tx_cpld_gnt;
reg										r_tx_mrd_gnt;
reg										r_tx_mwr_gnt;

assign fc_sel = r_fc_sel;
assign tx_cfg_gnt = 1'b1;

assign tx_cpld_gnt = r_tx_cpld_gnt;
assign tx_mrd_gnt = r_tx_mrd_gnt;
assign tx_mwr_gnt = r_tx_mwr_gnt;

always @ (posedge pcie_user_clk or negedge pcie_user_rst_n)
begin
	if(pcie_user_rst_n == 0)
		cur_state <= S_RX_AVAILABLE_FC_SEL;
	else
		cur_state <= next_state;
end

always @ (*)
begin
	case(cur_state)
		S_RX_AVAILABLE_FC_SEL: begin
			next_state <= S_TX_AVAILABLE_FC_SEL;
		end
		S_TX_AVAILABLE_FC_SEL: begin
			next_state <= S_RX_AVAILABLE_FC_SEL;
		end
		default: begin
			next_state <= S_RX_AVAILABLE_FC_SEL;
		end
	endcase
end

always @ (*)
begin
	case(cur_state)
		S_RX_AVAILABLE_FC_SEL: begin
			r_fc_sel <= 3'b000;
			r_rd_fc_sel <= 2'b01;
		end
		S_TX_AVAILABLE_FC_SEL: begin
			r_fc_sel <= 3'b100;
			r_rd_fc_sel <= 2'b10;
		end
		default: begin
			r_fc_sel <= 3'b000;
			r_rd_fc_sel <= 2'b00;
		end
	endcase
end

assign w_rx_available_fc_cpld = (r_rx_available_fc_cpld > P_RX_CONSTRAINT_FC_CPLD);
assign w_rx_available_fc_cplh = (r_rx_available_fc_cplh > P_RX_CONSTRAINT_FC_CPLH);

assign w_tx_available_fc_cpld = (r_tx_available_fc_cpld > P_TX_CONSTRAINT_FC_CPLD);
assign w_tx_available_fc_cplh = (r_tx_available_fc_cplh > P_TX_CONSTRAINT_FC_CPLH);
assign w_tx_available_fc_npd = (r_tx_available_fc_npd > P_TX_CONSTRAINT_FC_NPD);
assign w_tx_available_fc_nph = (r_tx_available_fc_nph > P_TX_CONSTRAINT_FC_NPH);
assign w_tx_available_fc_pd = (r_tx_available_fc_pd > P_TX_CONSTRAINT_FC_PD);
assign w_tx_available_fc_ph = (r_tx_available_fc_ph > P_TX_CONSTRAINT_FC_PH);

always @ (posedge pcie_user_clk)
begin
	r_tx_cpld_gnt <= w_tx_available_fc_cpld & w_tx_available_fc_cplh;
	r_tx_mrd_gnt <= (w_tx_available_fc_npd & w_tx_available_fc_nph) & (w_rx_available_fc_cpld & w_rx_available_fc_cplh);
	r_tx_mwr_gnt <= w_tx_available_fc_pd & w_tx_available_fc_ph;
end

always @ (posedge pcie_user_clk or negedge pcie_user_rst_n)
begin
	if(pcie_user_rst_n == 0) begin
		r_rd_fc_sel_d1 <= 0;
		r_rd_fc_sel_d2 <= 0;
	end
	else begin
		r_rd_fc_sel_d1 <= r_rd_fc_sel;
		r_rd_fc_sel_d2 <= r_rd_fc_sel_d1;
	end
end

always @ (posedge pcie_user_clk or negedge pcie_user_rst_n)
begin
	if(pcie_user_rst_n == 0) begin
		r_rx_available_fc_cpld <= 0;
		r_rx_available_fc_cplh <= 0;
		r_rx_available_fc_npd <= 0;
		r_rx_available_fc_nph <= 0;
		r_rx_available_fc_pd <= 0;
		r_rx_available_fc_ph <= 0;

		r_tx_available_fc_cpld <= 0;
		r_tx_available_fc_cplh <= 0;
		r_tx_available_fc_npd <= 0;
		r_tx_available_fc_nph <= 0;
		r_tx_available_fc_pd <= 0;
		r_tx_available_fc_ph <= 0;
	end
	else begin
		if(r_rd_fc_sel_d2[0] == 1) begin
			r_rx_available_fc_cpld <= fc_cpld;
			r_rx_available_fc_cplh <= fc_cplh;
			r_rx_available_fc_npd <= fc_npd;
			r_rx_available_fc_nph <= fc_nph;
			r_rx_available_fc_pd <= fc_pd;
			r_rx_available_fc_ph <= fc_ph;
		end
		if(r_rd_fc_sel_d2[1] == 1) begin
			r_tx_available_fc_cpld <= fc_cpld;
			r_tx_available_fc_cplh <= fc_cplh;
			r_tx_available_fc_npd <= fc_npd;
			r_tx_available_fc_nph <= fc_nph;
			r_tx_available_fc_pd <= fc_pd;
			r_tx_available_fc_ph <= fc_ph;
		end
	end
end



endmodule

