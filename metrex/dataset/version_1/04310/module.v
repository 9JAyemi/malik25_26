

module counterModulo(clk, modulo, count, oClk);
	parameter n = 10, safe = 1;
	input clk;
	input [n-1:0] modulo;
	output reg [n-1:0] count = 0;
	output oClk;
	
	assign oClk = count+1 == modulo ? 1 :
					count+1 < modulo ? 0 :
					safe ? 1 : 1'bx;

	always @(posedge clk)
		if (!oClk)
			count <= count + 1;
		else
			count <= 0;
endmodule

module vgaRotatingCounter(input clk, reset_,
									output reg [1:0] stage,
									output [9:0] count,
									output reg outClk);
	parameter ta = 96, tb = 16, tc = 640, td = 48;
	localparam A = 0, B = 1, C = 2, D = 3;

	wire stageClk;
	wire [9:0] modulo;
	
	assign modulo = stage == A ? ta :
						stage == B ? tb :
						stage == C ? tc :
						td;
	counterModulo #(10,0) c(clk, modulo, count, stageClk);
	
	always @(posedge clk)
		if (stageClk) begin
			if (stage == D)
				outClk <= 1;
			stage <= stage + 1;
		end else
		  outClk <= 0;
endmodule

module vgaControl(input clk, reset_,
						output reg VGA_VS, VGA_HS,
						output need,
						output [9:0] hNeed, vNeed);
	parameter n = 4;
	
	parameter ha = 120, hb = 64, hc = 800, hd = 56;
	parameter va = 6, vb = 23, vc = 600, vd = 37;

	wire [1:0] hStage, vStage;
	wire [9:0] hCount, vCount;
	wire hClock, vClock, vEnd;

	always @(posedge clk) begin
		VGA_HS <= hStage != 0;
		VGA_VS <= vStage != 0;
	end

	assign need = vStage == 2 && ((hStage == 2 && hCount != hc-1)
										|| (hStage == 1 && hCount == hb-1));

	assign hNeed = hStage == 2 ? hCount+1 : 0;
	assign vNeed = vCount;
	
	assign hClock = clk;
	vgaRotatingCounter #(ha, hb, hc, hd) h(hClock, 1, hStage, hCount, vClock);
	vgaRotatingCounter #(va, vb, vc, vd) v(vClock, 1, vStage, vCount, vEnd);
endmodule