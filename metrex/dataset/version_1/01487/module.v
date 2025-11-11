module mealy_state_machine (
  input clk,
  input reset,
  input in1,
  input in2,
  output reg out1,
  output reg out2
);

  parameter A = 3'b000, B = 3'b001, C = 3'b010, D = 3'b011, E = 3'b100;
  reg [2:0] state, next_state;
  
  always @(posedge clk, negedge reset) begin
    if (!reset) begin
      state <= A;
      out1 <= 1'b0;
      out2 <= 1'b0;
    end else begin
      state <= next_state;
      case (state)
        A: begin
          if (in1 == 1'b0 && in2 == 1'b0) begin
            next_state <= B;
            out1 <= 1'b1;
            out2 <= 1'b0;
          end else if (in1 == 1'b0 && in2 == 1'b1) begin
            next_state <= A;
            out1 <= 1'b0;
            out2 <= 1'b0;
          end else if (in1 == 1'b1 && in2 == 1'b0) begin
            next_state <= D;
            out1 <= 1'b0;
            out2 <= 1'b1;
          end else begin // in1 == 1'b1 && in2 == 1'b1
            next_state <= C;
            out1 <= 1'b1;
            out2 <= 1'b1;
          end
        end
        B: begin
          if (in1 == 1'b0 && in2 == 1'b0) begin
            next_state <= C;
            out1 <= 1'b0;
            out2 <= 1'b1;
          end else if (in1 == 1'b0 && in2 == 1'b1) begin
            next_state <= B;
            out1 <= 1'b0;
            out2 <= 1'b0;
          end else if (in1 == 1'b1 && in2 == 1'b0) begin
            next_state <= E;
            out1 <= 1'b1;
            out2 <= 1'b0;
          end else begin // in1 == 1'b1 && in2 == 1'b1
            next_state <= A;
            out1 <= 1'b0;
            out2 <= 1'b1;
          end
        end
        C: begin
          if (in1 == 1'b0 && in2 == 1'b0) begin
            next_state <= A;
            out1 <= 1'b1;
            out2 <= 1'b1;
          end else if (in1 == 1'b0 && in2 == 1'b1) begin
            next_state <= C;
            out1 <= 1'b0;
            out2 <= 1'b1;
          end else if (in1 == 1'b1 && in2 == 1'b0) begin
            next_state <= B;
            out1 <= 1'b1;
            out2 <= 1'b1;
          end else begin // in1 == 1'b1 && in2 == 1'b1
            next_state <= D;
            out1 <= 1'b0;
            out2 <= 1'b1;
          end
        end
        D: begin
          if (in1 == 1'b0 && in2 == 1'b0) begin
            next_state <= E;
            out1 <= 1'b0;
            out2 <= 1'b0;
          end else if (in1 == 1'b0 && in2 == 1'b1) begin
            next_state <= D;
            out1 <= 1'b0;
            out2 <= 1'b0;
          end else if (in1 == 1'b1 && in2 == 1'b0) begin
            next_state <= C;
            out1 <= 1'b1;
            out2 <= 1'b1;
          end else begin // in1 == 1'b1 && in2 == 1'b1
            next_state <= B;
            out1 <= 1'b0;
            out2 <= 1'b0;
          end
        end
        E: begin
          next_state <= E;
          if (in1 == 1'b0 && in2 == 1'b0) begin
            out1 <= 1'b1;
            out2 <= 1'b0;
          end else if (in1 == 1'b0 && in2 == 1'b1) begin
            out1 <= 1'b1;
            out2 <= 1'b0;
          end else if (in1 == 1'b1 && in2 == 1'b0) begin
            out1 <= 1'b0;
            out2 <= 1'b0;
          end else begin // in1 == 1'b1 && in2 == 1'b1
            out1 <= 1'b1;
            out2 <= 1'b0;
          end
        end
      endcase
    end
  end
  
endmodule
