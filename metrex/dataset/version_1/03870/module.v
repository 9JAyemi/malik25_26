
module divider(
reset,
out,
clk
);

output out;
input clk;
input reset;

parameter divisor1 = 5;
parameter divisor2 = 2;

reg[31:0] cnt1;
reg result;
wire EN;
wire compare1,compare2;


always@(posedge clk or negedge reset)
begin
   if(reset == 0)
      cnt1 <= 0;
	else if(cnt1 == divisor1)
		cnt1 <= 1;
	else
		cnt1 <= cnt1 + 1;
end

assign compare1 = (cnt1 == 5) ? 1 : 0;

assign compare2 = (cnt1 == divisor2) ? 1 : 0;

assign EN = compare1 | compare2;
 
always@(posedge clk or negedge reset)
begin
	if(reset == 0)
		result <= 0;
	else if(EN) 
	result <= !result;
		end

assign out = result;
endmodule

