// SVA for axis_rate_limit_64
// Bind with: bind axis_rate_limit_64 axis_rate_limit_64_asserts #(.DATA_WIDTH(DATA_WIDTH), .KEEP_WIDTH(KEEP_WIDTH)) i_axis_rate_limit_64_asserts (.*);

module axis_rate_limit_64_asserts #(
  parameter DATA_WIDTH = 64,
  parameter KEEP_WIDTH = (DATA_WIDTH/8)
)(
  input  wire                   clk,
  input  wire                   rst,

  input  wire [DATA_WIDTH-1:0]  input_axis_tdata,
  input  wire [KEEP_WIDTH-1:0]  input_axis_tkeep,
  input  wire                   input_axis_tvalid,
  input  wire                   input_axis_tready,
  input  wire                   input_axis_tlast,
  input  wire                   input_axis_tuser,

  output wire [DATA_WIDTH-1:0]  output_axis_tdata,
  output wire [KEEP_WIDTH-1:0]  output_axis_tkeep,
  output wire                   output_axis_tvalid,
  input  wire                   output_axis_tready,
  output wire                   output_axis_tlast,
  output wire                   output_axis_tuser,

  input  wire [7:0]             rate_num,
  input  wire [7:0]             rate_denom,
  input  wire                   rate_by_frame
);

default clocking cb @(posedge clk); endclocking
default disable iff (rst);

wire ihs = input_axis_tvalid  && input_axis_tready;
wire ohs = output_axis_tvalid && output_axis_tready;

// Basic reset behavior
assert property (@cb rst |-> (!output_axis_tvalid && !input_axis_tready));

// AXI-Stream stability on output when stalled
assert property (@cb output_axis_tvalid && !output_axis_tready |=> $stable({output_axis_tdata,output_axis_tkeep,output_axis_tlast,output_axis_tuser,output_axis_tvalid}));

// Optional upstream assumptions (comment out if not using formal)
// synopsys translate_off
`ifdef FORMAL
assume property (@cb input_axis_tvalid && !input_axis_tready |=> $stable({input_axis_tdata,input_axis_tkeep,input_axis_tlast,input_axis_tuser,input_axis_tvalid}));
`endif
// synopsys translate_on

// In/out beat counters and occupancy (difference)
logic [31:0] f_in_cnt, f_out_cnt;
always_ff @(posedge clk or posedge rst) begin
  if (rst) begin
    f_in_cnt  <= 0;
    f_out_cnt <= 0;
  end else begin
    if (ihs)  f_in_cnt  <= f_in_cnt  + 1;
    if (ohs)  f_out_cnt <= f_out_cnt + 1;
  end
end

// Outputs can never exceed accepted inputs
assert property (@cb f_out_cnt <= f_in_cnt);

// Scoreboard (depth 2) to ensure ordering and data integrity
logic [1:0]                 sb_occ;
logic [DATA_WIDTH-1:0]      sb_data [0:1];
logic [KEEP_WIDTH-1:0]      sb_keep [0:1];
logic                       sb_last [0:1];
logic                       sb_user [0:1];

always_ff @(posedge clk or posedge rst) begin
  if (rst) begin
    sb_occ <= 0;
  end else begin
    // Pop first (consume output)
    if (ohs) begin
      assert (sb_occ > 0);
      assert (output_axis_tdata == sb_data[0]);
      assert (output_axis_tkeep == sb_keep[0]);
      assert (output_axis_tlast == sb_last[0]);
      assert (output_axis_tuser == sb_user[0]);
      if (sb_occ == 2) begin
        sb_data[0] <= sb_data[1];
        sb_keep[0] <= sb_keep[1];
        sb_last[0] <= sb_last[1];
        sb_user[0] <= sb_user[1];
      end
      sb_occ <= sb_occ - 1;
    end
    // Push after pop (accept input)
    if (ihs) begin
      assert (sb_occ < 2); // no overflow beyond 2-deep buffering
      sb_data[sb_occ] <= input_axis_tdata;
      sb_keep[sb_occ] <= input_axis_tkeep;
      sb_last[sb_occ] <= input_axis_tlast;
      sb_user[sb_occ] <= input_axis_tuser;
      sb_occ <= sb_occ + 1;
    end
  end
end

// Difference equals occupancy and is bounded by 2
assert property (@cb (f_in_cnt - f_out_cnt) == sb_occ);
assert property (@cb (f_in_cnt - f_out_cnt) <= 2);

// If there is pending data, output must be asserting VALID
assert property (@cb (f_in_cnt - f_out_cnt) > 0 |-> output_axis_tvalid);
// If no pending data, output must be idle
assert property (@cb (f_in_cnt - f_out_cnt) == 0 |-> !output_axis_tvalid);

// Frame tracking on input/output (based on handshakes)
logic in_frame, out_frame;
always_ff @(posedge clk or posedge rst) begin
  if (rst) begin
    in_frame  <= 1'b0;
    out_frame <= 1'b0;
  end else begin
    if (ihs)  in_frame  <= ~input_axis_tlast;
    if (ohs)  out_frame <= ~output_axis_tlast;
  end
end

// In frame-by-frame mode, never throttle mid-frame when sink isn't backpressuring
// If sink is ready and output idle, input_ready must be high while in-frame and more beats remaining
assert property (@cb rate_by_frame && in_frame && input_axis_tvalid && !input_axis_tlast &&
                      output_axis_tready && !output_axis_tvalid |-> input_axis_tready);

// Output continuity: if sink remains ready, there must be no bubbles within an output frame
assert property (@cb out_frame && output_axis_tready |-> output_axis_tvalid);

// Coverage: observe throttling event (rate limiting) when sink is open
cover property (@cb !rate_by_frame ##1 output_axis_tready && !output_axis_tvalid &&
                     input_axis_tvalid && !input_axis_tready);

// Coverage: frame-based throttling between frames
cover property (@cb rate_by_frame ##1 ihs && !input_axis_tlast ##1 ihs && input_axis_tlast
                     ##1 !in_frame && output_axis_tready && !output_axis_tvalid &&
                     input_axis_tvalid && !input_axis_tready);

// Coverage: skid buffer depth of 2 exercised (occupancy reaches 2)
cover property (@cb sb_occ == 2);

// Coverage: backpressure holds output stable across multiple cycles
cover property (@cb output_axis_tvalid && !output_axis_tready ##1 output_axis_tvalid && !output_axis_tready);

endmodule