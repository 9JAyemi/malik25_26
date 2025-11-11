
module DataMemory(
    output reg [31:0] ReadData,
	 output reg [31:0] DATO1,
	 output reg [31:0] DATO2,
	 output reg [31:0] RESULTADO,
    input [31:0] Address,
    input [31:0] WriteData,
	 input [31:0] MouseData,
	 input MouseEnable,
    input WriteEnable,
    input CLK
    );

	reg [31:0] block [0:9];

	always @ (*) begin
		DATO1 = block[4];
		DATO2 = block[5];
		RESULTADO = block[7];
		if (CLK) begin
			case (Address)
				32'h00000000: ReadData = block[0];
				32'h00000004: ReadData = block[1];
				32'h00000008: ReadData = block[2];
				32'h0000000c: ReadData = block[3];
				32'h00000010: ReadData = block[4];
				32'h00000014: ReadData = block[5];
				32'h00000018: ReadData = block[6];
				32'h0000001c: ReadData = block[7];
				32'h00000020: ReadData = block[8];
				32'h00000024: ReadData = block[9];
				default: ReadData = 32'b0;
			endcase
		end
		else begin
			if (MouseEnable) begin
				block[1] = MouseData;
			end
			if (WriteEnable)
				case (Address)
					32'h00000000: block[0] = WriteData;
					32'h00000004: block[1] = WriteData;
					32'h00000008: block[2] = WriteData;
					32'h0000000c: block[3] = WriteData;
					32'h00000010: block[4] = WriteData;
					32'h00000014: block[5] = WriteData;
					32'h00000018: block[6] = WriteData;
					32'h0000001c: block[7] = WriteData;
					32'h00000020: block[8] = WriteData;
					32'h00000024: block[9] = WriteData;
				endcase
		end
	end
	
	integer i = 0;
	initial begin 
		for (i=0;i<10;i=i+1)
			block[i] = 32'b0;
		block[1] = 2;
		block[4] = 2;
	end

endmodule
