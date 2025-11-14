module fsm_longest_sequence_detection (
  input clk,
  input reset,
  input [7:0] data,
  output reg [2:0] longest_sequence
);

  parameter S0 = 3'b000, S1 = 3'b001, S2 = 3'b010, S3 = 3'b011, S4 = 3'b100;
  reg [2:0] state, next_state;
  
  always @(posedge clk) begin
    if (reset) begin
      state <= S0;
      longest_sequence <= 3'b000;
    end
    else begin
      state <= next_state;
      case (state)
        S0: begin
          if (data == 8'b00000000)
            next_state = S0;
          else if (data[7] == 1)
            next_state = S1;
          else
            next_state = S0;
        end
        S1: begin
          if (data == 8'b11111111) begin
            next_state = S4;
            longest_sequence <= 3'b111;
          end
          else if (data[7] == 1)
            next_state = S2;
          else
            next_state = S0;
        end
        S2: begin
          if (data == 8'b11111111) begin
            next_state = S4;
            longest_sequence <= 3'b111;
          end
          else if (data[7:6] == 2'b11)
            next_state = S3;
          else if (data[7] == 0)
            next_state = S0;
          else
            next_state = S2;
        end
        S3: begin
          if (data == 8'b11111111) begin
            next_state = S4;
            longest_sequence <= 3'b111;
          end
          else if (data[7] == 0)
            next_state = S0;
          else
            next_state = S3;
        end
        S4: begin
          if (data == 8'b11111111)
            next_state = S4;
          else
            next_state = S0;
        end
      endcase
    end
  end
  
endmodule
