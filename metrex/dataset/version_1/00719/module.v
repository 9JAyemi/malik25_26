module booth_multiplier (
  input clk,
  input reset,
  input start,
  input [15:0] A,
  input [15:0] B,
  output reg [31:0] P,
  output reg done
);

  reg [15:0] A_reg;
  reg [15:0] B_reg;
  reg [1:0] state;
  reg [4:0] count;
  reg [31:0] P_reg;
  wire [15:0] B_comp;
  wire [31:0] P_comp;

  assign B_comp = ~B + 1;
  assign P_comp = { {16{P_reg[31]}} , P_reg } + { {16{B_reg[15]}} , B_comp };

  always @(posedge clk) begin
    if (reset) begin
      state <= 2'b00;
      count <= 5'd0;
      P_reg <= 32'd0;
      done <= 1'b0;
    end else begin
      case (state)
        2'b00: begin // Idle state, waiting for start signal
          if (start) begin
            A_reg <= A;
            B_reg <= B;
            state <= 2'b01;
          end
        end
        2'b01: begin // Booth's algorithm state
          if (count < 5'd16) begin
            if (B_reg[0] == 1 && P_reg[0] == 0) begin
              P_reg <= P_reg + { {16{A_reg[15]}} , A_reg };
            end else if (B_reg[0] == 0 && P_reg[0] == 1) begin
              P_reg <= P_reg - { {16{A_reg[15]}} , A_reg };
            end
            B_reg <= { B_reg[15], B_reg[15:1] };
            count <= count + 1;
          end else begin
            state <= 2'b10;
          end
        end
        2'b10: begin // Output state
          P <= P_comp;
          done <= 1'b1;
          state <= 2'b00;
        end
        default: begin
          state <= 2'b00;
        end
      endcase
    end
  end
endmodule
