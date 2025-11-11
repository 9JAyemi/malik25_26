module master #(
	parameter	ADDR_WIDTH = 16,
	parameter	IPL_READ_ADDR = 16'h0,
	parameter	IPL_WRITE_ADDR = 16'h1,
	parameter	AW = ADDR_WIDTH - 1

)(
	input		clk_i,
	input		reset_i,

	input		dreq_i,
	output		dack_o,

	output	[AW:0]	adr_o,
	output		cyc_o,
	output		stb_o,
	output		we_o,
	input		ack_i
);

	reg	[AW:0]	adr_o;
	reg		stb_o;
	reg		we_o;

	reg	[AW:0]	rd_adr, wr_adr;
	reg		rd_cyc, wr_cyc;

	reg		dack_o;

	assign		cyc_o = rd_cyc | wr_cyc;

	always @(posedge clk_i) begin
		// Unless otherwise instructed, the following signals assume
		// these values on any given clock cycle.

		adr_o <= 0;
		stb_o <= 0;
		we_o <= 0;
		rd_cyc <= rd_cyc;
		wr_cyc <= wr_cyc;
		dack_o <= 0;

		// Upon reset, reset internal registers to their power-on
		// defaults.

		if(reset_i) begin
			rd_adr <= IPL_READ_ADDR;
			wr_adr <= IPL_WRITE_ADDR;
			rd_cyc <= 0;
			wr_cyc <= 0;
		end

		// Otherwise, implement the read/write state machine here.

		else begin
			// WARNING: THIS CODE IS NOT EXPRESSLY DESIGNED FOR
			// SINGLE-CYCLE TRANSACTIONS.  Experience on my
			// simulator shows that it works in practice; but, I
			// offer NO PROMISE that it'll work for you.  You'll
			// need to explore/experiment on your own.

			// If the DMAC isn't doing anything at the moment,
			// initiate a read cycle.  At this time, we acknowledge
			// the request for data to tell the slave that it's
			// in-progress.

			if(dreq_i && ~cyc_o) begin
				adr_o <= rd_adr;
				stb_o <= 1;
				rd_cyc <= 1;
				dack_o <= 1;
			end

			// If the read cycle is complete, then we kick off the
			// write cycle.

			if(rd_cyc && ack_i) begin
				rd_cyc <= 0;
				wr_cyc <= 1;
				adr_o <= wr_adr;
				stb_o <= 1;
				we_o <= 1;
			end

			// If the write cycle is complete, we sample the DREQ_I
			// signal.  If it's still asserted, kick off another
			// read cycle.	Otherwise, revert back to idle
			// condition.

			if(wr_cyc && ack_i) begin
				wr_cyc <= 0;
				if(dreq_i) begin
					adr_o <= rd_adr;
					stb_o <= 1;
					rd_cyc <= 1;
					dack_o <= 1;
				end
			end
		end
	end
endmodule