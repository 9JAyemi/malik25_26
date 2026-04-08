module fsm_3bit_pattern_detection (
  input clk,
  input reset,
  input [5:0] data,
  output reg match
);

  parameter S0 = 2'b00, S1 = 2'b01, S2 = 2'b10, S3 = 2'b11;
  reg [1:0] state, next_state;
  
  always @(posedge clk, posedge reset) begin
    if (reset) begin
      state <= S0;
      match <= 1'b0;
    end
    else begin
      state <= next_state;
      match <= (state == S3);
    end
  end
  
  always @(*) begin
    case (state)
      S0: begin
        if (data[2:0] == 3'b001) next_state = S1;
        else next_state = S0;
      end
      S1: begin
        if (data[2:0] == 3'b010) next_state = S2;
        else next_state = S0;
      end
      S2: begin
        if (data[2:0] == 3'b100) next_state = S3;
        else next_state = S0;
      end
      S3: begin
        next_state = S0;
      end
    endcase
  end
  
endmodule
