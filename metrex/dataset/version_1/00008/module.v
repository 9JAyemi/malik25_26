
module moore_machine (
  input clk,
  input reset,
  input x,
  input y,
  output reg [1:0] z
);

  // Define the states using one-hot encoding
  parameter A = 2'b00;
  parameter B = 2'b01;
  parameter C = 2'b10;

  // Define the state register and initialize to state A
  reg [1:0] state = A;

  // Define the state transition logic
  always @(posedge clk, posedge reset) begin
    if (reset) begin
      state <= A;
    end else begin
      case (state)
        A: begin
          if (x == 1 && y == 0) begin
            state <= B;
          end else if (x == 1 && y == 1) begin
            state <= C;
          end else begin
            state <= A;
          end
        end
        B: begin
          if (x == 1) begin
            state <= B;
          end else begin
            state <= A;
          end
        end
        C: begin
          if (x == 1) begin
            state <= C;
          end else begin
            state <= A;
          end
        end
      endcase
    end
  end

  // Define the output logic
  always @(state) begin
    case (state)
      A: z <= 2'b00;
      B: z <= 2'b01;
      C: z <= 2'b10;
    endcase
  end

endmodule