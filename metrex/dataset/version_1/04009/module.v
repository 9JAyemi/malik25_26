

(
input 	wire					CLK_I,
input		wire	[3:0]			D_I,
output	wire	[3:0]			D_O
);

genvar i;

		generate							
				for(i=3;i>=0;i=i-1)
				begin
					InputSync input_sync_inst
								(
								.CLK_I		(CLK_I),
								.D_I			(D_I[i]),
								.D_O			(D_O[i])
								);
				end
		endgenerate
		
endmodule

module InputSync
(
input		wire		D_I,
input		wire		CLK_I,
output	reg		D_O
);

reg 	[1:0]		sreg;

always@(posedge CLK_I)
		begin
			D_O	<=	sreg[1];
			sreg	<=	{sreg[0],D_I};
		end
			
endmodule

