module control_o (reset, rxd, StringReady, CharReady, parity, ready, error, WriteChar, WriteString, PossibleStart, clk_2, check);

   input rxd;
   input StringReady;
   input CharReady;
   input parity;
   input clk_2;
   input check;
   input reset;
   
   output reg ready;
   output reg error;
   output reg WriteChar;
   output reg WriteString;
   output reg PossibleStart;
  
   reg [2:0]  current_state;
   reg [2:0]  next_state;
   
   // se les ponen nombres a los estados para que en el case se pueda entender y manejar mejor
   parameter IDLE = 3'b000;
   parameter POSSIBLESTART = 3'b001;
   parameter READ = 3'b010;
   parameter ERROR = 3'b011;
   parameter WRITE = 3'b100;
   parameter STOP = 3'b101;

   always @(current_state or rxd or check or CharReady or StringReady or reset or parity) begin
      if (reset==1'b1) begin
	 next_state <= 3'b000;
	 ready =1'b0;
	 error = 1'b0;
	 WriteString = 1'b0;
	 WriteChar = 1'b0;
	 PossibleStart = 1'b0;

      end
      else begin
	 case (current_state)
	   IDLE: begin
	      if (rxd==1)
		next_state<=IDLE;
	      else
		next_state<=POSSIBLESTART;


	      ready=1'b0;
	      error=1'b0;
	      WriteChar=1'b0;
	      WriteString=1'b0;
	      PossibleStart=1'b0;
	   end // case: IDLE
	   
	   POSSIBLESTART: begin
	      if (check == 1) begin
		 if (rxd == 0) begin
		   next_state<=READ;
		end		
		 else
		   next_state<=IDLE;
	      end
	      else
		next_state<=POSSIBLESTART;

	      ready=1'b0;
	      error=1'b0;
	      WriteChar=1'b0;
	      WriteString=1'b0;
	      PossibleStart=1'b1;

	   end // case: POSSIBLESTART
	   
	   READ: begin
	      if (CharReady==0)
		next_state<=READ;
	      else
		next_state<=ERROR;

	      ready=1'b0;
	      error=1'b0;
	      WriteChar=1'b1;
	      WriteString=1'b0;
	      PossibleStart=1'b0;
	   end // case: READ
	   
	   ERROR: begin
	      next_state<=WRITE;
	      if (parity==1)
		error=1'b1;
	      else
		error=1'b0;

	      ready=1'b0;
	      WriteChar=1'b0;
	      WriteString=1'b0;
	      PossibleStart=1'b0;
	   end // case: ERROR
	   
	   WRITE: begin
	      if (StringReady==0)
		next_state<=IDLE;
	      else
		next_state<=STOP;

	      ready=1'b0;
	      error=1'b0;
	      WriteChar=1'b0;
	      WriteString=1'b1;
	      PossibleStart=1'b0;
	   end // case: WRITE
	   
	   STOP: begin
		next_state<=IDLE;

	      ready=1'b1;
	      error=1'b0;
	      WriteChar=1'b0;
	      WriteString=1'b0;
	      PossibleStart=1'b0;
	   end // case: STOP
	   
	   default: begin 
	      next_state<=IDLE;
	      ready=1'b0;
	      error=1'b0;
	      WriteChar=1'b0;
	      WriteString=1'b0;
	      PossibleStart=1'b0;
	   end
	 endcase // case (current_state)
      end // else: !if(reset==1'b1)
   end // always @ (posedge clk_2)
   
   always @(negedge clk_2 or posedge reset) begin
      if (reset == 1'b1) begin
	current_state<=IDLE;
	end
      else begin
	current_state<=next_state;
	end
   end
endmodule