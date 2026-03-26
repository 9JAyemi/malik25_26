
module alt_ddrx_clock_and_reset #
    ( parameter
        CTL_RESET_SYNC_STAGES      = 4,
        CTL_NUM_RESET_OUTPUT       = 1,
        CTL_HALF_RESET_SYNC_STAGES = 4,
        CTL_HALF_NUM_RESET_OUTPUT  = 1
    )
    (
        ctl_clk,
        ctl_reset_n,
        ctl_half_clk,
        ctl_half_clk_reset_n,
        
        resynced_ctl_reset_n,
        resynced_ctl_half_clk_reset_n
    );

input  ctl_clk;
input  ctl_reset_n;
input  ctl_half_clk;
input  ctl_half_clk_reset_n;

output [CTL_NUM_RESET_OUTPUT      - 1 : 0] resynced_ctl_reset_n;
output [CTL_HALF_NUM_RESET_OUTPUT - 1 : 0] resynced_ctl_half_clk_reset_n;

alt_ddrx_reset_sync #(
    .RESET_SYNC_STAGES (CTL_RESET_SYNC_STAGES),
    .NUM_RESET_OUTPUT  (CTL_NUM_RESET_OUTPUT)
) reset_sync_inst (
	.reset_n           (ctl_reset_n),
	.clk               (ctl_clk),
	.reset_n_sync      (resynced_ctl_reset_n)
);

alt_ddrx_reset_sync #(
    .RESET_SYNC_STAGES (CTL_HALF_RESET_SYNC_STAGES),
    .NUM_RESET_OUTPUT  (CTL_HALF_NUM_RESET_OUTPUT)
) half_reset_sync_inst (
	.reset_n           (ctl_half_clk_reset_n),
	.clk               (ctl_half_clk),
	.reset_n_sync      (resynced_ctl_half_clk_reset_n)
);


endmodule

module alt_ddrx_reset_sync #
    ( parameter
        RESET_SYNC_STAGES = 4,
        NUM_RESET_OUTPUT  = 1
    )
    (
    	reset_n,
    	clk,
    	reset_n_sync
    );

input	reset_n;
input	clk;
output	[NUM_RESET_OUTPUT-1:0] reset_n_sync;

 reg	[RESET_SYNC_STAGES+NUM_RESET_OUTPUT-2:0] reset_reg ;

generate
genvar i;
	for (i=0; i<RESET_SYNC_STAGES+NUM_RESET_OUTPUT-1; i=i+1)
	begin: reset_stage
		always @(posedge clk or negedge reset_n)
		begin
			if (~reset_n)
				reset_reg[i] <= 1'b0;
			else
			begin
				if (i==0)
					reset_reg[i] <= 1'b1;
				else if (i < RESET_SYNC_STAGES)
					reset_reg[i] <= reset_reg[i-1];
				else
					reset_reg[i] <= reset_reg[RESET_SYNC_STAGES-2];
				
			end
		end
	end
endgenerate

	assign reset_n_sync = reset_reg[RESET_SYNC_STAGES+NUM_RESET_OUTPUT-2:RESET_SYNC_STAGES-1];

endmodule

