module iq_comp (
	input clk, RESETn,
	input freeze_iqcomp,				input [1:0] op_mode,
	input [3:0] Ix, Qx,
	input signed [12:0] Wr_in, Wj_in,	output reg signed [3:0] Iy, Qy,		output wire settled,				output reg signed [12:0] Wr, Wj
);

localparam BYPASS = 2'b00;
localparam INT_W = 2'b01;
localparam EXT_W = 2'b10;
localparam CONT_W = 2'b11;				wire signed [3:0] Ix_s;
wire signed [3:0] Qx_s;

wire [3:0] M;

wire signed [12:0] Wr_use;
wire signed [12:0] Wj_use;
reg signed [3:0] I_math;
reg signed [3:0] Q_math;
wire signed [12:0] Wr_math;
wire signed [12:0] Wj_math;

wire signed [25:0] I_math_intermediate1;
wire signed [25:0] Q_math_intermediate1;
wire signed [4:0] I_math_intermediate2;
wire signed [4:0] Q_math_intermediate2;
wire signed [25:0] Ix_s_shifted;
wire signed [25:0] Qx_s_shifted;

assign settled = freeze_iqcomp;		assign M = 4'd9;					assign Ix_s = Ix - 4'd8;
assign Qx_s = Qx - 4'd8;

assign Wr_use = (op_mode == INT_W) ? Wr : Wr_in;
assign Wj_use = (op_mode == INT_W) ? Wj : Wj_in;

assign Ix_s_shifted = $signed(Ix_s) <<< M;
assign Qx_s_shifted = $signed(Qx_s) <<< M;

assign I_math_intermediate1 = Ix_s_shifted + $signed(((Wr_use * Ix_s) + (Wj_use * Qx_s)));
assign Q_math_intermediate1 = Qx_s_shifted + $signed(((Wj_use * Ix_s) - (Wr_use * Qx_s)));

assign I_math_intermediate2 = $signed(I_math_intermediate1) >>> M;
assign Q_math_intermediate2 = $signed(Q_math_intermediate1) >>> M;

always @(*) begin
	if($signed(I_math_intermediate2) < $signed(0-5'd8)) begin
		I_math = $signed(-4'd8);
	end
	else if($signed(I_math_intermediate2) > $signed(5'd7)) begin
		I_math = $signed(4'd7);
	end
	else begin
		I_math = $signed(I_math_intermediate2);
	end

	if($signed(Q_math_intermediate2) < $signed(0-5'd8)) begin
		Q_math = $signed(-4'd8);
	end
	else if($signed(Q_math_intermediate2) > $signed(5'd7)) begin
		Q_math = $signed(4'd7);
	end
	else begin
		Q_math = $signed(Q_math_intermediate2);
	end
end

assign Wr_math = $signed(Wr - ((Iy + Qy) * (Iy - Qy)));
assign Wj_math = $signed(Wj - 2 * Iy * Qy);

always @(posedge clk) begin
	if(~RESETn) begin
		Iy <= 0;
		Qy <= 0;
		Wr <= 0;
		Wj <= 0;
	end else begin
		case (op_mode)
			BYPASS: begin
				Iy <= Ix_s;
				Qy <= Qx_s;
				Wr <= 0;
				Wj <= 0;
			end
			INT_W: begin 
				Iy <= I_math;
				Qy <= Q_math;
				if(freeze_iqcomp) begin 
					Wr <= Wr;
					Wj <= Wj;
				end else begin
					Wr <= Wr_math;
					Wj <= Wj_math;
				end
			end
			EXT_W: begin
				Iy <= I_math;
				Qy <= Q_math;
				Wr <= Wr_use;	Wj <= Wj_use;	end
			CONT_W: begin		Iy <= Ix_s;
				Qy <= Qx_s;
				Wr <= 0;
				Wj <= 0;
			end
			default : ;
		endcase
	end
end
endmodule 

