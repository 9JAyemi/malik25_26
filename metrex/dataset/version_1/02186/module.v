
module clk_synchronizer#(
	parameter	SYSCLK_FREQ_HZ		= 64'd100_000_000,
	parameter	PPS_HIGH_LEVEL_US	= 64'd10_000,
	parameter	GENCLK_FREQ_HZ		= 1,
	parameter	FORWARD_OFFSET_CLK	= 0
)(
	input		clk,
	input		rst_n,
	input		pps_in,
	output		sync_clk_out,
	output		clk_sync_ok_out
);

function integer log2ceil;
input reg [63 : 0] val;
reg [63 : 0] i;
begin
	i = 1;
	log2ceil = 0;
	while (i < val) begin
		log2ceil = log2ceil + 1;
		i = i << 1;
	end
end
endfunction

localparam						DUTY_CNT_N	= SYSCLK_FREQ_HZ * PPS_HIGH_LEVEL_US / 64'd1_000_000;
localparam						DIVIDER_NUM	= SYSCLK_FREQ_HZ / GENCLK_FREQ_HZ;
localparam						DIVIDER_BIT	= log2ceil(DIVIDER_NUM);

reg								clk_sync_flag;
reg								rst_release;
wire							rst_pps_rst;
reg								rst_pps;
reg		[DIVIDER_BIT - 1 : 0]	clk_divider;
wire							clk_gen_forward;
reg								clk_generated;

always @ (posedge pps_in or posedge rst_pps_rst)
begin
	if (rst_pps_rst) begin
		rst_pps <= 0;
	end
	else begin
		rst_pps <= 1;
	end
end

always @ (posedge clk or negedge rst_n)
begin
	if (!rst_n) begin
		rst_release <= 0;
	end
	else if ((rst_pps == 1) || (clk_sync_flag == 1)) begin
		rst_release <= 1;
	end
	else begin
		rst_release <= 0;
	end
end

always @ (posedge clk or negedge rst_n)
begin
	if (!rst_n) begin
		clk_sync_flag <= 0;
	end
	else if (rst_release == 1) begin
		clk_sync_flag <= 1;
	end
	else begin
		clk_sync_flag <= clk_sync_flag;
	end
end

always @ (posedge clk or posedge rst_pps)
begin
	if (rst_pps) begin
		clk_divider <= FORWARD_OFFSET_CLK + 2;
	end
	else if (clk_divider < DIVIDER_NUM - 1) begin
		clk_divider <= clk_divider + 1'b1;
	end
	else begin
		clk_divider <= 0;
	end
end

always @ (posedge clk or negedge rst_n)
begin
	if (!rst_n) begin
		clk_generated <= 0;
	end
	else if (clk_sync_flag) begin
		clk_generated <= clk_gen_forward;
	end
	else begin
		clk_generated <= 0;
	end
end

assign rst_pps_rst = rst_release | (~rst_n);
assign clk_gen_forward = (clk_divider < DUTY_CNT_N) ? 1'b1: 1'b0;
assign clk_sync_ok_out = clk_sync_flag;
assign sync_clk_out = clk_generated;

endmodule
