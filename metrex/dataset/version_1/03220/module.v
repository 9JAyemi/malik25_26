module FSM #(
  parameter n = 2, // number of output signals
  parameter m = 2, // number of input signals
  parameter s = 4 // number of states in the original FSM
)(
  input clk, // clock signal
  input rst, // reset signal
  input [m-1:0] in, // input signals
  output reg [n-1:0] out // output signals
);


reg [s-1:0] state; // current state of the FSM

// define the states of the FSM
parameter STATE_0 = 2'b00;
parameter STATE_1 = 2'b01;
parameter STATE_2 = 2'b10;
parameter STATE_3 = 2'b11;

// define the sub-states of STATE_0
parameter STATE_0_SUB_0 = 3'b000;
parameter STATE_0_SUB_1 = 3'b001;

// define the sub-states of STATE_1
parameter STATE_1_SUB_0 = 3'b010;
parameter STATE_1_SUB_1 = 3'b011;

// define the sub-states of STATE_2
parameter STATE_2_SUB_0 = 3'b100;
parameter STATE_2_SUB_1 = 3'b101;

// define the sub-states of STATE_3
parameter STATE_3_SUB_0 = 3'b110;
parameter STATE_3_SUB_1 = 3'b111;

// define the next state logic for each state and sub-state
always @(posedge clk, posedge rst) begin
  if (rst) begin
    state <= STATE_0;
  end else begin
    case (state)
      STATE_0: begin
        if (in[0] && in[1]) begin
          state <= STATE_1_SUB_0;
        end else if (in[0]) begin
          state <= STATE_0_SUB_1;
        end else begin
          state <= STATE_0_SUB_0;
        end
      end
      STATE_1_SUB_0: begin
        if (in[1]) begin
          state <= STATE_2_SUB_0;
        end else begin
          state <= STATE_1_SUB_1;
        end
      end
      STATE_1_SUB_1: begin
        if (in[0]) begin
          state <= STATE_0_SUB_0;
        end else begin
          state <= STATE_1_SUB_0;
        end
      end
      STATE_2_SUB_0: begin
        if (in[0] && in[1]) begin
          state <= STATE_3_SUB_0;
        end else if (in[1]) begin
          state <= STATE_2_SUB_1;
        end else begin
          state <= STATE_2_SUB_0;
        end
      end
      STATE_2_SUB_1: begin
        if (in[0]) begin
          state <= STATE_1_SUB_1;
        end else begin
          state <= STATE_2_SUB_0;
        end
      end
      STATE_3_SUB_0: begin
        if (in[0]) begin
          state <= STATE_0_SUB_1;
        end else if (in[1]) begin
          state <= STATE_3_SUB_1;
        end else begin
          state <= STATE_3_SUB_0;
        end
      end
      STATE_3_SUB_1: begin
        if (in[0] && in[1]) begin
          state <= STATE_1_SUB_0;
        end else begin
          state <= STATE_3_SUB_0;
        end
      end
    endcase
  end
end

// define the output logic for each state and sub-state
always @* begin
  case (state)
    STATE_0_SUB_0: begin
      out[0] <= 1'b0;
      out[1] <= 1'b0;
    end
    STATE_0_SUB_1: begin
      out[0] <= 1'b0;
      out[1] <= 1'b1;
    end
    STATE_1_SUB_0: begin
      out[0] <= 1'b1;
      out[1] <= 1'b0;
    end
    STATE_1_SUB_1: begin
      out[0] <= 1'b1;
      out[1] <= 1'b1;
    end
    STATE_2_SUB_0: begin
      out[0] <= 1'b0;
      out[1] <= 1'b1;
    end
    STATE_2_SUB_1: begin
      out[0] <= 1'b1;
      out[1] <= 1'b0;
    end
    STATE_3_SUB_0: begin
      out[0] <= 1'b1;
      out[1] <= 1'b1;
    end
    STATE_3_SUB_1: begin
      out[0] <= 1'b0;
      out[1] <= 1'b0;
    end
  endcase
end

endmodule