module sequential_logic_block (
  input clk,
  input reset,
  input [2:0] x,
  output reg f
);

  parameter state0 = 3'b000;
  parameter state1 = 3'b001;
  parameter state2 = 3'b010;
  parameter state3 = 3'b011;
  parameter state4 = 3'b100;
  parameter state5 = 3'b101;
  parameter state6 = 3'b110;
  parameter state7 = 3'b111;

  reg [2:0] state;
  always @(posedge clk, posedge reset) begin
    if (reset) begin
      state <= state0;
      f <= 1'b0;
    end else begin
      case (state)
        state0: begin
          f <= 1'b0;
          state <= state0;
        end
        state1: begin
          if (x == 3'b001) begin
            f <= 1'b1;
            state <= state2;
          end else begin
            f <= 1'b0;
            state <= state0;
          end
        end
        state2: begin
          if (x == 3'b010) begin
            f <= 1'b1;
            state <= state3;
          end else begin
            f <= 1'b0;
            state <= state0;
          end
        end
        state3: begin
          if (x == 3'b011) begin
            f <= 1'b1;
            state <= state4;
          end else begin
            f <= 1'b0;
            state <= state0;
          end
        end
        state4: begin
          f <= 1'b0;
          state <= state0;
        end
        state5: begin
          if (x == 3'b001) begin
            f <= 1'b1;
            state <= state6;
          end else begin
            f <= 1'b0;
            state <= state0;
          end
        end
        state6: begin
          if (x == 3'b010) begin
            f <= 1'b1;
            state <= state7;
          end else begin
            f <= 1'b0;
            state <= state0;
          end
        end
        state7: begin
          if (x == 3'b011) begin
            f <= 1'b1;
            state <= state0;
          end else begin
            f <= 1'b0;
            state <= state0;
          end
        end
      endcase
    end
  end

endmodule
