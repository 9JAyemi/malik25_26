
module enemyPosition(
	input clk,
	input frameClk,
	input isEnemyActive,
	input wire [7:0] _randomSeed,
	input [3:0] uid,
	output reg [9:0] enemyPositionX,
	output reg [8:0] enemyPositionY
);
	parameter top = 20;
	parameter bottom = 440;
	parameter center = 220;
	parameter left = 20;
	parameter right = 600;
	parameter middle = 300;
	parameter north = 2'b00;
	parameter south = 2'b01;
	parameter west = 2'b10;
	parameter east = 2'b11;

	
	reg [1:0] enemyDirectionFrom;
	reg [1:0] enemyDirectionTo;
	reg recentEnemyActive;
	reg [10:0] randomSeed;

	initial begin
		enemyPositionX     =  'd0;
		enemyPositionY     =  'd0;
		enemyDirectionFrom = 2'b00;
		enemyDirectionTo   = 2'b00;
		recentEnemyActive  = 1'b0;
		randomSeed         = 'd0;
	end

	always @(posedge frameClk) begin
		randomSeed = (_randomSeed[6:0] * uid)+uid;
		if(isEnemyActive == 1'b1) begin
			case(recentEnemyActive)
				1'b0: begin
					enemyDirectionFrom <= randomSeed[1:0];
					enemyDirectionTo   <= randomSeed[3:2];
					if(enemyDirectionFrom == enemyDirectionTo) begin
						enemyDirectionTo <= enemyDirectionFrom + 1;
					end

					case(enemyDirectionFrom)
						north: begin if (randomSeed[3] == 1'b1) begin
								enemyPositionX <= middle + (randomSeed[2:0] * 30);
							end else begin
								enemyPositionX <= middle - (randomSeed[2:0] * 30);
							end
							enemyPositionY <= top+1;
						end
						south: begin if (randomSeed[3] == 1'b1) begin
								enemyPositionX <= middle + (randomSeed[2:0] * 30);
							end else begin
								enemyPositionX <= middle - (randomSeed[2:0] * 30);
							end
							enemyPositionY <= bottom-1;
						end
						west: begin enemyPositionX <= left+1;
							if (randomSeed[3] == 1'b1) begin
								enemyPositionY <= center + (randomSeed[2:0] * 25);
							end else begin
								enemyPositionY <= center - (randomSeed[2:0] * 25);
							end
							end
						east: begin enemyPositionX <= right-1;
							if (randomSeed[3] == 1'b1) begin
								enemyPositionY <= center + (randomSeed[2:0] * 25);
							end else begin
								enemyPositionY <= center - (randomSeed[2:0] * 25);
							end
							end
					endcase
					recentEnemyActive <= 1'b1;
				end
				1'b1: begin
					if (enemyPositionX >= left && enemyPositionX <= right && enemyPositionY >= top && enemyPositionY <= bottom) begin
						case(enemyDirectionFrom)
							north: begin enemyPositionY <= enemyPositionY + 1;
							end
							south: begin enemyPositionY <= enemyPositionY - 1;
							end
							west: begin enemyPositionX <= enemyPositionX + 1;
							end
							east: begin enemyPositionX <= enemyPositionX - 1;
							end
						endcase
						case(enemyDirectionTo)
							north: begin enemyPositionY <= enemyPositionY - 1;
								end
							south: begin enemyPositionY <= enemyPositionY + 1;
								end
							west: begin enemyPositionX <= enemyPositionX - 1;
								end
							east: begin enemyPositionX <= enemyPositionX + 1;
								end
						endcase
					end else begin
						enemyDirectionFrom <= enemyDirectionTo;
						enemyDirectionTo   <= randomSeed[3:2];
						if(enemyDirectionFrom == enemyDirectionTo) begin
							enemyDirectionTo <= enemyDirectionFrom + 1;
						end

						if (enemyPositionY > top) begin
							enemyPositionY <= enemyPositionY - 2;
						end else begin
							enemyPositionY <= top + 2;
						end
						
						if (enemyPositionX > left) begin
							enemyPositionX <= enemyPositionX - 2;
						end else begin
							enemyPositionX <= left + 2;
						end

						case(enemyDirectionFrom)
							north: begin enemyPositionY <= enemyPositionY + 2;
							end
							south: begin enemyPositionY <= enemyPositionY - 2;
							end
							west: begin enemyPositionX <= enemyPositionX + 2;
							end
							east: begin enemyPositionX <= enemyPositionX - 2;
							end
						endcase
					end
				end
			endcase
		end else begin
			enemyPositionX     <=  'd0;
			enemyPositionY     <=  'd0;
			enemyDirectionFrom <= 2'b00;
			enemyDirectionTo   <= 2'b00;
			recentEnemyActive  <= 1'b0;
		end
	end
endmodule
