

module log2_table
	(
	input	     	clk,			input		trilinear_en, 		input	[31:0]	val, 			output	[9:0]	log2
	);


	reg	[3:0]	int_mm_no;
	reg	[5:0]	lod_fract;

	wire		 over_flow;
	wire	[9:0]	 log_in;

	assign log_in = val[17:8];
	assign over_flow = |val[31:18];



always @(posedge clk) begin
	casex ({over_flow, log_in})
		11'b0_10xxxxxxx_x, 11'b0_011xxxxxx_x:	begin if(trilinear_en && log_in[9]) begin
				int_mm_no <= 4'h9; 
				lod_fract <= val[16:11];
			end 
			else begin
				int_mm_no <= 4'h8;
				lod_fract <= val[15:10];
			end
		end	
		11'b0_010xxxxxx_x, 11'b0_0011xxxxx_x: begin if(trilinear_en && log_in[8]) begin
				int_mm_no <= 4'h8; 
				lod_fract <= val[15:10];
			end 
			else begin
				int_mm_no <= 4'h7;
				lod_fract <= val[14:9];
			end
		end
		11'b0_0010xxxxx_x, 11'b0_00011xxxx_x:	begin if(trilinear_en && log_in[7]) begin
				int_mm_no <= 4'h7; 
				lod_fract <= val[14:9];
			end 
			else begin
				int_mm_no <= 4'h6;
				lod_fract <= val[13:8];
			end
		end
		11'b0_00010xxxx_x, 11'b0_000011xxx_x:	begin if(trilinear_en && log_in[6]) begin
				int_mm_no <= 4'h6; 
				lod_fract <= val[13:8];
			end 
			else begin
				int_mm_no <= 4'h5;
				lod_fract <= val[12:7];
			end
		end
		11'b0_000010xxx_x, 11'b0_0000011xx_x:	begin if(trilinear_en && log_in[5]) begin
				int_mm_no <= 4'h5; 
				lod_fract <= val[12:7];
			end 
			else begin
				int_mm_no <= 4'h4;
				lod_fract <= val[11:6];
			end
		end
		11'b0_0000010xx_x, 11'b0_00000011x_x:	begin if(trilinear_en && log_in[4]) begin
				int_mm_no <= 4'h4; 
				lod_fract <= val[11:6];
			end 
			else begin
				int_mm_no <= 4'h3;
				lod_fract <= val[10:5];
			end
		end
		11'b0_00000010x_x, 11'b0_000000011_x:	begin if(trilinear_en && log_in[3]) begin
				int_mm_no <= 4'h3; 
				lod_fract <= val[10:5];
			end 
			else begin
				int_mm_no <= 4'h2;
				lod_fract <= val[9:4];
			end
		end
		11'b0_000000010_x, 11'b0_000000001_1:	begin if(trilinear_en && log_in[2]) begin
				int_mm_no <= 4'h2; 
				lod_fract <= val[9:4];
			end 
			else begin
				int_mm_no <= 4'h1;
				lod_fract <= val[8:3];
			end
		end
		11'b0_000000001_0, 11'b0_000000000_x:	begin if(trilinear_en && log_in[1]) begin
				int_mm_no <= 4'h1; 
				lod_fract <= val[8:3];
			end 
			else begin
				int_mm_no <= 4'h0;
				lod_fract <= val[7:2];
			end
		end
		default: begin
				int_mm_no <= 4'h9; 
				lod_fract <= val[16:11];
		end
	endcase
end

assign log2 = {int_mm_no, lod_fract};


endmodule
