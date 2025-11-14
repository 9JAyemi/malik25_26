module state_splitting_FSM #(
  parameter n = 4, // number of states
  parameter m = 2 // number of output signals
) (
  input clk,
  input [n-1:0] in,
  output [m-1:0] out
);

reg [1:0] state; // current state
reg [1:0] next_state; // next state
reg [m-1:0] output_reg; // output register

// Define the states
parameter STATE_00 = 2'b00;
parameter STATE_01 = 2'b01;
parameter STATE_10 = 2'b10;
parameter STATE_11 = 2'b11;

// Define the state transitions
always @(posedge clk) begin
  case (state)
    STATE_00: begin
      if (in[0] && in[1]) begin
        next_state = STATE_11;
      end else if (in[0]) begin
        next_state = STATE_01;
      end else if (in[1]) begin
        next_state = STATE_10;
      end else begin
        next_state = STATE_00;
      end
    end
    STATE_01: begin
      if (in[0] && in[1]) begin
        next_state = STATE_11;
      end else if (in[1]) begin
        next_state = STATE_00;
      end else begin
        next_state = STATE_01;
      end
    end
    STATE_10: begin
      if (in[0] && in[1]) begin
        next_state = STATE_11;
      end else if (in[0]) begin
        next_state = STATE_00;
      end else begin
        next_state = STATE_10;
      end
    end
    STATE_11: begin
      if (!in[0] && !in[1]) begin
        next_state = STATE_00;
      end else if (!in[0]) begin
        next_state = STATE_10;
      end else if (!in[1]) begin
        next_state = STATE_01;
      end else begin
        next_state = STATE_11;
      end
    end
  endcase
end

// Define the output signals
always @(state) begin
  case (state)
    STATE_00: begin
      output_reg[0] = 1'b0;
      output_reg[1] = 1'b0;
    end
    STATE_01: begin
      output_reg[0] = 1'b0;
      output_reg[1] = 1'b1;
    end
    STATE_10: begin
      output_reg[0] = 1'b1;
      output_reg[1] = 1'b0;
    end
    STATE_11: begin
      output_reg[0] = 1'b1;
      output_reg[1] = 1'b1;
    end
  endcase
end

// Assign the outputs
assign out = output_reg;

// Update the state
always @(posedge clk) begin
  state <= next_state;
end

endmodule