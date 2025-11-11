

module controller(
  clock, reset, run,
  wrSize, config_data,
  validIn, dataIn, busy, arm, 
  send, memoryWrData, memoryRead, 
  memoryWrite, memoryLastWrite);

input clock;
input reset;
input run;
input wrSize;
input [31:0] config_data;
input validIn;
input [31:0] dataIn;
input busy;
input arm;

output send;
output [31:0] memoryWrData;
output memoryRead;
output memoryWrite;
output memoryLastWrite;

reg [15:0] fwd, next_fwd; reg [15:0] bwd, next_bwd;

reg send, next_send;
reg memoryRead, next_memoryRead;
reg memoryWrite, next_memoryWrite;
reg memoryLastWrite, next_memoryLastWrite;

reg [17:0] counter, next_counter; 
wire [17:0] counter_inc = counter+1'b1;


reg [31:0] memoryWrData, next_memoryWrData;
always @(posedge clock) 
begin
  memoryWrData = next_memoryWrData;
end
always @*
begin
  #1; next_memoryWrData = dataIn;
end



parameter [2:0]
  IDLE =     3'h0,
  SAMPLE =   3'h1,
  DELAY =    3'h2,
  READ =     3'h3,
  READWAIT = 3'h4;

reg [2:0] state, next_state; 

initial state = IDLE;
always @(posedge clock or posedge reset) 
begin
  if (reset)
    begin
      state = IDLE;
      memoryWrite = 1'b0;
      memoryLastWrite = 1'b0;
      memoryRead = 1'b0;
    end
  else 
    begin
      state = next_state;
      memoryWrite = next_memoryWrite;
      memoryLastWrite = next_memoryLastWrite;
      memoryRead = next_memoryRead;
    end
end

always @(posedge clock)
begin
  counter = next_counter;
  send = next_send;
end

always @*
begin
  #1;
  next_state = state;
  next_counter = counter;
  next_memoryWrite = 1'b0;
  next_memoryLastWrite = 1'b0;
  next_memoryRead = 1'b0;
  next_send = 1'b0;

  case(state)
    IDLE :
      begin
        next_counter = 0;
        next_memoryWrite = 1;
	if (run) next_state = DELAY;
	else if (arm) next_state = SAMPLE;
      end

    SAMPLE : 
      begin
        next_counter = 0;
        next_memoryWrite = validIn;
        if (run) next_state = DELAY;
      end

    DELAY : 
      begin
	if (validIn)
	  begin
	    next_memoryWrite = 1'b1;
            next_counter = counter_inc;
            if (counter == {fwd,2'b11}) 	begin				next_memoryLastWrite = 1'b1;	next_counter = 0;
		next_state = READ;
	      end
	  end
      end

    READ : 
      begin
        next_memoryRead = 1'b1;
        next_send = 1'b1;
        if (counter == {bwd,2'b11}) 
	  begin
            next_counter = 0;
            next_state = IDLE;
          end
        else 
	  begin
            next_counter = counter_inc;
            next_state = READWAIT;
          end
      end

    READWAIT : 
      begin
        if (!busy && !send) next_state = READ;
      end
  endcase
end


always @(posedge clock) 
begin
  fwd = next_fwd;
  bwd = next_bwd;
end

always @*
begin
  #1;
  next_fwd = fwd;
  next_bwd = bwd;

  if (wrSize) 
    begin
      next_fwd = config_data[31:16];
      next_bwd = config_data[15:0];
    end
end
endmodule

