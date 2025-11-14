
module AllignAdderProcess(
	input [31:0] z_postSpecial,
	input [3:0] Opcode_Special,
	input idle_Special,
	input [35:0] cout_Special,
	input [35:0] zout_Special,
	input [31:0] sout_Special,
	input [7:0] difference_Special,
	input [7:0] InsTagSpecial,
	input clock,
	output reg idle_Allign,
	output reg [35:0] cout_Allign,
	output reg [35:0] zout_Allign,
	output reg [31:0] sout_Allign,
	output reg [3:0] Opcode_Allign,
	output reg [31:0] z_postAllign,
	output reg [7:0] InsTagAllign
   );

parameter no_idle = 1'b0,
			 put_idle = 1'b1;

wire z_sign;
wire [7:0] z_exponent;
wire [26:0] z_mantissa;

wire c_sign;
wire [7:0] c_exponent;
wire [26:0] c_mantissa;

assign z_sign = zout_Special[35];
assign z_exponent = zout_Special[34:27] - 127;
assign z_mantissa = {zout_Special[26:0]};

assign c_sign = cout_Special[35];
assign c_exponent = cout_Special[34:27] - 127;
assign c_mantissa = {cout_Special[26:0]};

parameter sin_cos		= 4'd0,
			 sinh_cosh	= 4'd1,
			 arctan		= 4'd2,
			 arctanh		= 4'd3,
			 exp			= 4'd4,
			 sqr_root   = 4'd5,			division	= 4'd6,
			 tan			= 4'd7,			tanh			= 4'd8,			nat_log		= 4'd9,			hypotenuse = 4'd10,
			 PreProcess = 4'd11;


always @ (posedge clock)
begin
	
	InsTagAllign <= InsTagSpecial;
	Opcode_Allign <= Opcode_Special;
	z_postAllign <= z_postSpecial;
		
	idle_Allign <= idle_Special;
	sout_Allign <= sout_Special;
	
	if (idle_Special != put_idle) begin
		if ($signed(c_exponent) > $signed(z_exponent)) begin
			zout_Allign[35] <= zout_Special[35];
			zout_Allign[34:27] <= z_exponent + difference_Special + 127;
			zout_Allign[26:0] <= z_mantissa >> difference_Special;
			zout_Allign[0] <= z_mantissa[0] | z_mantissa[1];
			cout_Allign <= cout_Special;
		end else if ($signed(c_exponent) <= $signed(z_exponent)) begin
			cout_Allign[35] <= cout_Special[35];
			cout_Allign[34:27] <= c_exponent + difference_Special + 127;
			cout_Allign[26:0] <= c_mantissa >> difference_Special;
			cout_Allign[0] <= c_mantissa[0] | c_mantissa[1];
			zout_Allign <= zout_Special;
		 end		
	end
	
	else begin
		zout_Allign <= zout_Special;
		cout_Allign <= cout_Special;
	end
	end

endmodule
