module sector_to_flash_map(
	input [2:0] sector,
	output reg [2:0] flash_sector
);

	parameter SECTOR1_MAP = 3'b001;
	parameter SECTOR2_MAP = 3'b010;
	parameter SECTOR3_MAP = 3'b011;
	parameter SECTOR4_MAP = 3'b100;
	parameter SECTOR5_MAP = 3'b101;

	always @(*) begin
		case(sector)
			3'd1: flash_sector = SECTOR1_MAP;
			3'd2: flash_sector = SECTOR2_MAP;
			3'd3: flash_sector = SECTOR3_MAP;
			3'd4: flash_sector = SECTOR4_MAP;
			3'd5: flash_sector = SECTOR5_MAP;
			default: flash_sector = 3'd0;
		endcase;
	end

endmodule