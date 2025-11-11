`define REG_SIZE 20
module initial_config(

iCLK, iRST_n, oINITIAL_START,
iINITIAL_ENABLE,
);


input iCLK;
input iRST_n;
output oINITIAL_START;
input	iINITIAL_ENABLE;

wire oINITIAL_START;
reg [`REG_SIZE-1:0] cnt;

always@(posedge iCLK or negedge iRST_n)
	begin
		if (!iRST_n)
			begin 
				cnt <= 0;
			end
		else if (cnt == 20'hfffff)

			begin
				cnt <=20'hfffff;

			end
		else
			begin
				cnt <= cnt + 1;	
			end
	end
	
	
assign oINITIAL_START = ((cnt == 20'hffffe)&iINITIAL_ENABLE) ? 1'b1: 1'b0;


endmodule




