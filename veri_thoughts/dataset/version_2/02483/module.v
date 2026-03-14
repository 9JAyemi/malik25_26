
module CounterChainCore(
  input        clock,
  input        reset,
  output [9:0] io_out_0,
  output [9:0] io_out_1,
  output [9:0] io_next_1,
  input        io_enable_0,
  output       io_done_0
);
  wire  counters_0_clock;
  wire  counters_0_reset;
  wire [9:0] counters_0_io_out;
  wire [9:0] counters_0_io_next;
  wire  counters_0_io_enable;
  wire  counters_0_io_done;
  wire [9:0] counters_0_io_config_max;
  wire  _T_55;
  wire  _GEN_0;
  Counter counters_0 (
    .clock(counters_0_clock),
    .reset(counters_0_reset),
    .io_out(counters_0_io_out),
    .io_next(counters_0_io_next),
    .io_enable(counters_0_io_enable),
    .io_done(counters_0_io_done),
    .io_config_max(counters_0_io_config_max)
  );
  assign _T_55 = counters_0_io_done;
  assign _GEN_0 = io_enable_0;
  assign io_out_0 = counters_0_io_out;
  assign io_out_1 = _T_55 ? 10'h1 : 10'h0;
  assign io_next_1 = _T_55 ? 10'h2 : 10'h1;
  assign io_done_0 = counters_0_io_done;
  assign counters_0_io_enable = _GEN_0;
  assign counters_0_io_config_max = 10'h9;
  assign counters_0_clock = clock;
  assign counters_0_reset = reset;
endmodule
module Counter(
  input        clock,
  input        reset,
  output [9:0] io_out,
  output [9:0] io_next,
  input        io_enable,
  output       io_done,
  input [9:0]  io_config_max
);
  reg [9:0] reg_value;
  wire [9:0] wire_next_value;
  assign io_out = reg_value;
  assign io_next = wire_next_value;
  assign io_done = (wire_next_value == io_config_max);
  assign wire_next_value = io_enable ? (reg_value + 10'h1) : reg_value;
  always @(posedge clock) begin
    if(reset) begin
      reg_value <= 10'h0;
    end else begin
      if(io_enable) begin
        reg_value <= wire_next_value;
      end
    end
  end
endmodule