module chatgpt_generate_edge_detect(
  input               clk,
  input               rst_n,
  input               a,
  input               select,
  output reg          rise,
  output reg          fall
);

  // State definitions
  parameter IDLE = 2'b00;
  parameter RISE_DETECT = 2'b01;
  parameter FALL_DETECT = 2'b10;

  // State register and next state logic
  reg [1:0] state, next_state;
  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      state <= IDLE;
    end else begin
      state <= next_state;
    end
  end

  // Output register and logic
  reg active_edge;
  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      active_edge <= 1'b0;
    end else begin
      case (state)
        IDLE: begin
          active_edge <= 1'b0;
        end
        RISE_DETECT: begin
          active_edge <= 1'b1;
        end
        FALL_DETECT: begin
          active_edge <= 1'b0;
        end
      endcase
    end
  end

  // State transition logic
  always @(*) begin
    case (state)
      IDLE: begin
        if (select) begin
          if (a) begin
            next_state = RISE_DETECT;
          end else begin
            next_state = FALL_DETECT;
          end
        end else begin
          next_state = IDLE;
        end
      end
      RISE_DETECT: begin
        if (~a) begin
          next_state = IDLE;
        end else begin
          next_state = RISE_DETECT;
        end
      end
      FALL_DETECT: begin
        if (a) begin
          next_state = IDLE;
        end else begin
          next_state = FALL_DETECT;
        end
      end
    endcase
  end

  // Output logic
  always @(posedge clk, negedge rst_n) begin
    if (~rst_n) begin
      rise <= 1'b0;
      fall <= 1'b0;
    end else begin
      case (state)
        IDLE: begin
          rise <= 1'b0;
          fall <= 1'b0;
        end
        RISE_DETECT: begin
          rise <= 1'b1;
          fall <= 1'b0;
        end
        FALL_DETECT: begin
          rise <= 1'b0;
          fall <= 1'b1;
        end
      endcase
    end
  end

endmodule