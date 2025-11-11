module fsm_4bit_sequence_detection (
  input clk,
  input reset,
  input [3:0] data,
  output reg match
);

  // Define the states
  parameter STATE_0 = 2'b00;
  parameter STATE_1 = 2'b01;
  parameter STATE_2 = 2'b10;
  parameter STATE_3 = 2'b11;

  // Define the state register and next state logic
  reg [1:0] state, next_state;

  always @ (posedge clk) begin
    if (reset) begin
      state <= STATE_0;
    end else begin
      state <= next_state;
    end
  end

  // Define the output logic
  always @ (state, data) begin
    match = 0;
    case (state)
      STATE_0: begin
        if (data == 4'b0001) begin
          next_state = STATE_1;
        end else begin
          next_state = STATE_0;
        end
      end
      STATE_1: begin
        if (data == 4'b0010) begin
          next_state = STATE_2;
        end else begin
          next_state = STATE_0;
        end
      end
      STATE_2: begin
        if (data == 4'b0100) begin
          next_state = STATE_3;
          match = 1;
        end else begin
          next_state = STATE_0;
        end
      end
      STATE_3: begin
        if (data == 4'b1000) begin
          next_state = STATE_0;
        end else begin
          next_state = STATE_0;
        end
      end
    endcase
  end

endmodule
