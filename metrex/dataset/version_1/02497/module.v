module sample_generator (
  input wire [7:0] FrameSize,
  input wire En,
  input wire AXI_En,
  output wire [31:0] m_axis_tdata,
  output wire [3:0] m_axis_tstrb,
  output wire m_axis_tlast,
  output wire m_axis_tvalid,
  input wire m_axis_tready,
  input wire m_axis_aclk,
  input wire m_axis_aresetn,
  input wire [31:0] s_axis_tdata,
  input wire [3:0] s_axis_tstrb,
  input wire s_axis_tlast,
  input wire s_axis_tvalid,
  output wire s_axis_tready,
  input wire s_axis_aclk,
  input wire s_axis_aresetn
);

  // Local parameters
  localparam IDLE = 0, START = 1, DATA = 2, END = 3;
  
  // Local variables
  reg [7:0] frame_count = 0;
  reg [31:0] data_count = 0;
  reg [31:0] data = 0;
  reg [3:0] strb = 0;
  reg [1:0] state = IDLE;
  reg valid = 0;
  reg last = 0;
  
  // AXI4Stream interface
  assign s_axis_tready = (state == DATA) ? m_axis_tready : 1'b0;
  assign m_axis_tdata = data;
  assign m_axis_tstrb = strb;
  assign m_axis_tlast = last;
  assign m_axis_tvalid = valid;
  
  // State machine
  always @(posedge m_axis_aclk) begin
    if (!m_axis_aresetn) begin
      frame_count <= 0;
      data_count <= 0;
      data <= 0;
      strb <= 0;
      state <= IDLE;
      valid <= 0;
      last <= 0;
    end else begin
      case (state)
        IDLE: begin
          if (En && AXI_En) begin
            frame_count <= frame_count + 1;
            data_count <= 0;
            state <= START;
          end
        end
        START: begin
          valid <= 1;
          if (s_axis_tready) begin
            state <= DATA;
          end
        end
        DATA: begin
          valid <= 1;
          data_count <= data_count + 4;
          data <= data_count;
          strb <= 4'b1111;
          if (data_count + 4 >= FrameSize) begin
            last <= 1;
            state <= END;
          end
        end
        END: begin
          valid <= 1;
          if (s_axis_tready) begin
            last <= 0;
            if (frame_count == 255) begin
              state <= IDLE;
            end else begin
              state <= START;
            end
          end
        end
      endcase
    end
  end

endmodule