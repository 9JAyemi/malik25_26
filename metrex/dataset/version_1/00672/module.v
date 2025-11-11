module fsm_0101_sequence_detection (
  input clk,
  input reset,
  input data,
  output reg match
);

  // Define the states
  parameter STATE_IDLE = 2'b00;
  parameter STATE_WAIT_1 = 2'b01;
  parameter STATE_WAIT_2 = 2'b10;
  parameter STATE_MATCH = 2'b11;
  
  // Define the state register and next state logic
  reg [1:0] state, next_state;
  
  always @ (posedge clk) begin
    if (reset) begin
      state <= STATE_IDLE;
    end else begin
      state <= next_state;
    end
  end
  
  // Define the next state logic
  always @ (*) begin
    case (state)
      STATE_IDLE: begin
        if (data == 1'b0) begin
          next_state = STATE_WAIT_1;
        end else begin
          next_state = STATE_IDLE;
        end
      end
      
      STATE_WAIT_1: begin
        if (data == 1'b1) begin
          next_state = STATE_WAIT_2;
        end else begin
          next_state = STATE_IDLE;
        end
      end
      
      STATE_WAIT_2: begin
        if (data == 1'b0) begin
          next_state = STATE_MATCH;
        end else begin
          next_state = STATE_IDLE;
        end
      end
      
      STATE_MATCH: begin
        next_state = STATE_IDLE;
      end
    endcase
  end
  
  // Define the match output
  always @ (*) begin
    if (state == STATE_MATCH) begin
      match = 1'b1;
    end else begin
      match = 1'b0;
    end
  end
  
endmodule
