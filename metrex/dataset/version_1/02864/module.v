module mealy_fsm (
  input clk,
  input reset,
  input in1,
  input in2,
  output reg out,
  output reg [2:0] state
);

  // Define the states
  parameter A = 3'b000;
  parameter B = 3'b001;
  parameter C = 3'b010;
  parameter D = 3'b011;
  parameter E = 3'b100;

  // Define the state transition table
  always @(posedge clk) begin
    if (reset) begin
      state <= A;
      out <= 0;
    end else begin
      case (state)
        A: begin
          if (in1 == 0 && in2 == 0) begin
            state <= B;
            out <= 0;
          end else if (in1 == 0 && in2 == 1) begin
            state <= A;
            out <= 0;
          end else if (in1 == 1 && in2 == 0) begin
            state <= C;
            out <= 1;
          end else if (in1 == 1 && in2 == 1) begin
            state <= D;
            out <= 0;
          end
        end
        B: begin
          if (in1 == 0 && in2 == 0) begin
            state <= A;
            out <= 0;
          end else if (in1 == 0 && in2 == 1) begin
            state <= B;
            out <= 0;
          end else if (in1 == 1 && in2 == 0) begin
            state <= C;
            out <= 1;
          end else if (in1 == 1 && in2 == 1) begin
            state <= D;
            out <= 0;
          end
        end
        C: begin
          if (in1 == 0 && in2 == 0) begin
            state <= A;
            out <= 0;
          end else if (in1 == 0 && in2 == 1) begin
            state <= B;
            out <= 0;
          end else if (in1 == 1 && in2 == 0) begin
            state <= C;
            out <= 1;
          end else if (in1 == 1 && in2 == 1) begin
            state <= D;
            out <= 0;
          end
        end
        D: begin
          if (in1 == 0 && in2 == 0) begin
            state <= A;
            out <= 0;
          end else if (in1 == 0 && in2 == 1) begin
            state <= B;
            out <= 0;
          end else if (in1 == 1 && in2 == 0) begin
            state <= C;
            out <= 1;
          end else if (in1 == 1 && in2 == 1) begin
            state <= D;
            out <= 0;
          end
        end
      endcase
    end
  end

endmodule
