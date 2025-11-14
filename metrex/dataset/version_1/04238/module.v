
module Ethernet_MAC #(
  parameter n = 8, // number of input signals
  parameter m = 8 // number of output signals
)(
  input [n-1:0] data_in,
  input [47:0] dest_mac,
  input [47:0] src_mac,
  input clk,
  input reset,
  output reg [n-1:0] data_out,
  output reg [47:0] dest_mac_out,
  output reg [47:0] src_mac_out,
  output reg tx_en,
  output reg rx_en
);

reg [7:0] preamble = 8'h55; // Ethernet preamble
reg [31:0] sfd = 32'hD5C5D5C5; // Ethernet Start Frame Delimiter

reg [47:0] dest_mac_reg; // register for storing destination MAC address
reg [47:0] src_mac_reg; // register for storing source MAC address
reg [n-1:0] data_reg; // register for storing data

reg [31:0] frame_cnt; // counter for tracking the number of bits in a frame
reg [3:0] state; // state machine state

parameter IDLE = 4'b0000; // idle state
parameter PREAMBLE = 4'b0001; // preamble state
parameter SFD = 4'b0010; // start frame delimiter state
parameter DEST_MAC = 4'b0011; // destination MAC address state
parameter SRC_MAC = 4'b0100; // source MAC address state
parameter LENGTH = 4'b0101; // length state
parameter DATA = 4'b0110; // data state
parameter FCS = 4'b0111; // frame check sequence state

always @(posedge clk) begin
  if (reset) begin
    state <= IDLE;
    frame_cnt <= 0;
    tx_en <= 0;
    rx_en <= 0;
  end else begin
    case (state)
      IDLE: begin
        tx_en <= 0;
        rx_en <= 1;
        if (data_in != 0) begin
          state <= PREAMBLE;
          frame_cnt <= 0;
          dest_mac_reg <= dest_mac;
          src_mac_reg <= src_mac;
          data_reg <= data_in;
        end
      end
      PREAMBLE: begin
        tx_en <= 1;
        rx_en <= 0;
        if (frame_cnt == 7) begin
          state <= SFD;
          frame_cnt <= 0;
        end else begin
          data_out <= preamble;
          frame_cnt <= frame_cnt + 1;
        end
      end
      SFD: begin
        tx_en <= 1;
        rx_en <= 0;
        if (frame_cnt == 31) begin
          state <= DEST_MAC;
          frame_cnt <= 0;
        end else begin
          data_out <= sfd[frame_cnt];
          frame_cnt <= frame_cnt + 1;
        end
      end
      DEST_MAC: begin
        tx_en <= 1;
        rx_en <= 0;
        if (frame_cnt == 47) begin
          state <= SRC_MAC;
          frame_cnt <= 0;
        end else begin
          data_out <= dest_mac_reg[frame_cnt];
          frame_cnt <= frame_cnt + 1;
        end
      end
      SRC_MAC: begin
        tx_en <= 1;
        rx_en <= 0;
        if (frame_cnt == 95) begin
          state <= LENGTH;
          frame_cnt <= 0;
        end else begin
          data_out <= src_mac_reg[frame_cnt-48];
          frame_cnt <= frame_cnt + 1;
        end
      end
      LENGTH: begin
        tx_en <= 1;
        rx_en <= 0;
        if (frame_cnt == 111) begin
          state <= DATA;
          frame_cnt <= 0;
        end else begin
          data_out <= 0;
          frame_cnt <= frame_cnt + 1;
        end
      end
      DATA: begin
        tx_en <= 1;
        rx_en <= 0;
        if (frame_cnt == (n*8)-1) begin
          state <= FCS;
          frame_cnt <= 0;
        end else begin
          data_out <= data_reg[frame_cnt-112];
          frame_cnt <= frame_cnt + 1;
        end
      end
      FCS: begin
        tx_en <= 1;
        rx_en <= 0;
        if (frame_cnt == 127) begin
          state <= IDLE;
          frame_cnt <= 0;
        end else begin
          data_out <= 0;
          frame_cnt <= frame_cnt + 1;
        end
      end
    endcase
  end
end

// Assign output registers
always @(posedge clk) begin
  if (reset) begin
    dest_mac_out <= 0;
    src_mac_out <= 0;
  end else begin
    if (state == IDLE) begin
      dest_mac_out <= dest_mac;
      src_mac_out <= src_mac;
    end
  end
end

endmodule