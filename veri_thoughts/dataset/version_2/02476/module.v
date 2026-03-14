
module bus_fsm (
	output reg gnt,
	output reg [1:0] state,
	input dly,
	input done,
	input req,
	input clk,
	input rst_n
);

	// Define the states of the FSM
	parameter [1:0] IDLE = 2'b00,
					BBUSY = 2'b01,
					BWAIT = 2'b10,
					BFREE = 2'b11;

	// Declare the state and next state variables
	reg [1:0] state, next_state;

	// Initialize the state and next state variables
	initial begin
		state <= IDLE;
		next_state <= IDLE;
	end

	// Assign the next state to the current state on the positive clock edge
	always @(posedge clk or negedge rst_n) begin
		if (!rst_n) begin
			state <= IDLE;
		end
		else begin
			state <= next_state;
		end
	end

	// Implement the FSM logic using a case statement
	always @(*) begin
		case (state)
			IDLE: if (req) next_state = BBUSY; else next_state = IDLE;
			BBUSY: if (!done) next_state = BBUSY; else if (dly) next_state = BWAIT; else next_state = BFREE;
			BWAIT: if (!dly) next_state = BFREE; else next_state = BWAIT;
			BFREE: if (req) next_state = BBUSY; else next_state = IDLE;
			default: next_state = IDLE;
		endcase
		gnt = (state == BBUSY) | (state == BWAIT);
	end
endmodule