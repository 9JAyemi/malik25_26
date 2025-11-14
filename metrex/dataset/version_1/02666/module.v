
module axi_data_mover (
  input clk,
  input resetn,

  input [2:0] request_id,
  output [2:0] response_id,
  input sync_id,
  input eot,

  input enable,
  output reg enabled,

  output xfer_req,

  output s_axi_ready,
  input s_axi_valid,
  input [63:0] s_axi_data,

  input m_axi_ready,
  output m_axi_valid,
  output [63:0] m_axi_data,
  output m_axi_last,

  input req_valid,
  output reg req_ready,
  input [3:0] req_last_burst_length
);

parameter MAX_BEATS_PER_BURST = 16;

reg [3:0] last_burst_length = 0;
reg [3:0] beat_counter = 0;
reg [2:0] id = 0;
reg [2:0] id_next = 0;

reg pending_burst = 0;
reg active = 0;
reg last_eot = 0;
reg last_non_eot = 0;

wire last_load;
wire last;

assign xfer_req = active;

assign response_id = id;

assign last = eot ? last_eot : last_non_eot;

assign s_axi_ready = m_axi_ready & pending_burst & active;
assign m_axi_valid = s_axi_valid & pending_burst & active;
assign m_axi_data = s_axi_data;
assign m_axi_last = last;

assign last_load = (m_axi_ready & s_axi_valid & active) & (last_eot | last_non_eot);

// fixed to drive req_ready
always @( posedge clk )
  if ( req_valid & ~active )
    req_ready <= 1'b0;
  else
    req_ready <= 1'b1;

always @(posedge clk) begin
  if (resetn == 1'b0) begin
    enabled <= 1'b0;
  end else begin
    if (enable) begin
      enabled <= 1'b1;
    end else begin
      enabled <= 1'b0;
    end
  end
end

always @(posedge clk) begin
  if (req_valid && ~active) begin
    id_next <= id + 1;
    beat_counter <= 1;
    last_burst_length <= req_last_burst_length;
    pending_burst <= 1;
    active <= 1;
  end else if (s_axi_ready && s_axi_valid && active) begin
    beat_counter <= beat_counter + 1;
    if (beat_counter == last_burst_length) begin
      last_eot <= 1;
      last_non_eot <= 0;
    end else if (beat_counter == MAX_BEATS_PER_BURST - 1) begin
      last_eot <= 0;
      last_non_eot <= 1;
    end else begin
      last_eot <= 0;
      last_non_eot <= 0;
    end
  end else if (last_load) begin
    active <= 0;
    pending_burst <= 0;
  end
end

always @(posedge clk) begin
  if (resetn == 1'b0) begin
    id <= 0;
  end else begin
    id <= id_next;
  end
end

endmodule