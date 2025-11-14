

module adapter_rgb_2_ppfifo #(
  parameter                 DATA_WIDTH = 24
)(
  input                             clk,
  input                             rst,

  input         [23:0]              i_rgb,
  input                             i_h_sync,
  input                             i_h_blank,
  input                             i_v_sync,
  input                             i_v_blank,
  input                             i_data_en,

  output                            o_ppfifo_clk,
  input       [1:0]                 i_ppfifo_rdy,
  output  reg [1:0]                 o_ppfifo_act,
  input       [23:0]                i_ppfifo_size,
  output  reg                       o_ppfifo_stb,
  output  reg [DATA_WIDTH - 1:0]    o_ppfifo_data


);
localparam      IDLE        = 0;
localparam      READY       = 1;
localparam      RELEASE     = 2;

reg           [23:0]        r_count;
reg           [2:0]         state;
assign  o_ppfifo_clk    = clk;
always @ (posedge clk) begin
  o_ppfifo_stb          <=  0;
  if (rst) begin
    r_count             <=  0;
    o_ppfifo_act        <=  0;
    o_ppfifo_data       <=  0;
    state               <=  IDLE;
  end
  else begin
    case (state)
      IDLE: begin
        o_ppfifo_act    <=  0;
        if ((i_ppfifo_rdy > 0) && (o_ppfifo_act == 0)) begin
          r_count           <=  0;
          if (i_ppfifo_rdy[0]) begin
            o_ppfifo_act[0] <=  1;
          end
          else begin
            o_ppfifo_act[1] <=  1;
          end
          state             <=  READY;
        end
      end
      READY: begin
        if (r_count < i_ppfifo_size) begin
          if (!i_h_blank) begin
            o_ppfifo_stb    <=  1;
            o_ppfifo_data   <=  i_rgb;

            r_count         <=  r_count + 1;
          end
        end
        else begin
          state             <=  RELEASE;
        end
        if (r_count > 0 && i_h_blank) begin
          state             <=  RELEASE;
        end
      end
      RELEASE: begin
        o_ppfifo_act        <=  0;
        state               <=  IDLE;
      end
      default: begin
      end
    endcase
  end
end



endmodule
