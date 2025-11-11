module mealy_fsm (
  input clk,
  input reset,
  input in1,
  input in2,
  output reg out
);

  parameter A = 2'b00;
  parameter B = 2'b01;
  parameter C = 2'b10;
  parameter D = 2'b11;
  
  reg [1:0] state, next_state;
  
  always @(posedge clk) begin
    if (reset) begin
      state <= A;
    end else begin
      state <= next_state;
    end
  end
  
  always @(*) begin
    case (state)
      A: begin
        if (in1 == 1 && in2 == 1) begin
          next_state = D;
          out = 0;
        end else begin
          if (in1 == 1) begin
            next_state = C;
            out = 1;
          end else if (in2 == 1) begin
            next_state = B;
            out = 0;
          end else begin
            next_state = A;
            out = 0;
          end
        end
      end
      B: begin
        if (in1 == 1 && in2 == 1) begin
          next_state = D;
          out = 0;
        end else begin
          if (in1 == 1) begin
            next_state = C;
            out = 1;
          end else if (in2 == 1) begin
            next_state = B;
            out = 0;
          end else begin
            next_state = B;
            out = 0;
          end
        end
      end
      C: begin
        if (in1 == 1 && in2 == 1) begin
          next_state = D;
          out = 0;
        end else begin
          if (in1 == 1) begin
            next_state = C;
            out = 1;
          end else if (in2 == 1) begin
            next_state = B;
            out = 0;
          end else begin
            next_state = C;
            out = 1;
          end
        end
      end
      D: begin
        if (in1 == 1 && in2 == 1) begin
          next_state = D;
          out = 0;
        end else begin
          if (in1 == 1) begin
            next_state = C;
            out = 1;
          end else if (in2 == 1) begin
            next_state = B;
            out = 0;
          end else begin
            next_state = D;
            out = 0;
          end
        end
      end
      default: begin
        next_state = A;
        out = 0;
      end
    endcase
  end
  
endmodule
