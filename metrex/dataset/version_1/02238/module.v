module SERIAL_OUT(CLK,BYTEIN,ADDR,READ,READY,CLEAR,RX_D,RESET);
input CLK,READY,RESET;
input [7:0]BYTEIN;
output reg RX_D,READ,CLEAR=1;
output reg [4:0]ADDR=0;

reg [9:0] data_out=0;
reg [6:0] count=0;

always@(posedge CLK or negedge RESET)
begin

	if(RESET==0)
		begin
		count=0;
		ADDR=0;
		CLEAR=1;
		READ=0;
		RX_D=1;
		end
	else
		begin
		if(READY==1)
			begin
			data_out[0]=0;
			data_out[1]=BYTEIN[0];
			data_out[2]=BYTEIN[1];
			data_out[3]=BYTEIN[2];
			data_out[4]=BYTEIN[3];
			data_out[5]=BYTEIN[4];
			data_out[6]=BYTEIN[5];
			data_out[7]=BYTEIN[6];
			data_out[8]=BYTEIN[7];
			data_out[9]=1;
			
			if(count==9)
				begin
				READ=1;
				count=0;
				RX_D=1;
				end
			else if(count==8)
				begin
				RX_D=data_out[count];
				count=count+1;
				READ=0;
				ADDR=ADDR+1;
				if(ADDR==32)
					begin
						ADDR=0;
						CLEAR=0;
					end
				end
			else
				begin
				RX_D=data_out[count];
				count=count+1;
				READ=0;
				end
			end
		else
			begin
			CLEAR=1;
			ADDR=0;
			RX_D=1;
			end
		end

end

endmodule

			

			