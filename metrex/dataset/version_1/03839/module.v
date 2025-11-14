

module controller (
  input  wire        clock,
  input  wire        reset,
  input  wire        run,
  input  wire        wrSize,
  input  wire [31:0] config_data,
  input  wire        validIn,
  input  wire [31:0] dataIn,
  input  wire        busy,
  input  wire        arm,
  output reg         send,
  output reg  [31:0] memoryWrData,
  output reg         memoryRead,
  output reg         memoryWrite,
  output reg         memoryLastWrite
);

reg [15:0] fwd; reg [15:0] bwd;

reg next_send;
reg next_memoryRead;
reg next_memoryWrite;
reg next_memoryLastWrite;

reg [17:0] counter, next_counter; 
wire [17:0] counter_inc = counter+1'b1;

always @(posedge clock) 
memoryWrData <= dataIn;

localparam [2:0]
  IDLE =     3'h0,
  SAMPLE =   3'h1,
  DELAY =    3'h2,
  READ =     3'h3,
  READWAIT = 3'h4;

reg [2:0] state, next_state; 

initial state = IDLE;
always @(posedge clock, posedge reset) 
if (reset) begin
  state           <= IDLE;
  memoryWrite     <= 1'b0;
  memoryLastWrite <= 1'b0;
  memoryRead      <= 1'b0;
end else begin
  state           <= next_state;
  memoryWrite     <= next_memoryWrite;
  memoryLastWrite <= next_memoryLastWrite;
  memoryRead      <= next_memoryRead;
end

always @(posedge clock)
begin
  counter <= next_counter;
  send    <= next_send;
end

always @*
begin
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
if (wrSize) {fwd, bwd} <= config_data[31:0];

endmodule
