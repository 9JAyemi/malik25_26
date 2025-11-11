module pipelined_edge_detect(
  input               clk,
  input               rst_n,
  input               a,
  input               delay,
  output reg          rise,
  output reg          fall
);

  reg [1:0]           state;
  reg                 a_delayed;
  reg                 a_delayed2;

  parameter           IDLE = 2'b00;
  parameter           RISE_DETECT = 2'b01;
  parameter           FALL_DETECT = 2'b10;

  always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state <= IDLE;
      a_delayed <= 1'b0;
      a_delayed2 <= 1'b0;
      rise <= 1'b0;
      fall <= 1'b0;
    end
    else begin
      case (state)
        IDLE: begin
          a_delayed <= a;
          a_delayed2 <= a_delayed;
          if (a_delayed2 == 1'b0 && a_delayed == 1'b1) begin
            rise <= 1'b1;
            fall <= 1'b0;
            state <= RISE_DETECT;
          end
          else if (a_delayed2 == 1'b1 && a_delayed == 1'b0) begin
            rise <= 1'b0;
            fall <= 1'b1;
            state <= FALL_DETECT;
          end
          else begin
            rise <= 1'b0;
            fall <= 1'b0;
            state <= IDLE;
          end
        end
        RISE_DETECT: begin
          a_delayed <= a;
          a_delayed2 <= a_delayed;
          if (a_delayed2 == 1'b1 && a_delayed == 1'b1) begin
            rise <= 1'b0;
            fall <= 1'b0;
            state <= IDLE;
          end
          else if (a_delayed2 == 1'b0 && a_delayed == 1'b1) begin
            rise <= 1'b1;
            fall <= 1'b0;
            state <= RISE_DETECT;
          end
          else begin
            rise <= 1'b0;
            fall <= 1'b0;
            state <= IDLE;
          end
        end
        FALL_DETECT: begin
          a_delayed <= a;
          a_delayed2 <= a_delayed;
          if (a_delayed2 == 1'b0 && a_delayed == 1'b0) begin
            rise <= 1'b0;
            fall <= 1'b0;
            state <= IDLE;
          end
          else if (a_delayed2 == 1'b1 && a_delayed == 1'b0) begin
            rise <= 1'b0;
            fall <= 1'b1;
            state <= FALL_DETECT;
          end
          else begin
            rise <= 1'b0;
            fall <= 1'b0;
            state <= IDLE;
          end
        end
      endcase
    end
  end

endmodule