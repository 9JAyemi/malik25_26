// SVA for probe_decoder
// Bind this to the DUT for checks and coverage

module probe_decoder_sva (
  input logic        clk,
  input logic [63:0] probe0,
  input logic [63:0] probe1,
  input logic [15:0] device_out,
  input logic [47:0] action_out
);

  // Helper: expected decode functions
  function automatic logic [15:0] exp_dev (input logic [15:0] p);
    case (p)
      16'h0001: exp_dev = 16'h0001;
      16'h0002: exp_dev = 16'h0002;
      16'h0003: exp_dev = 16'h0003;
      16'h0004: exp_dev = 16'h0004;
      default:  exp_dev = 16'hFFFF;
    endcase
  endfunction

  function automatic logic [47:0] exp_act (input logic [47:0] p);
    case (p)
      48'h000000000001: exp_act = 48'h000000000001;
      48'h000000000002: exp_act = 48'h000000000002;
      48'h000000000003: exp_act = 48'h000000000003;
      48'h000000000004: exp_act = 48'h000000000004;
      48'h000000000005: exp_act = 48'h000000000005;
      48'h000000000006: exp_act = 48'h000000000006;
      default:          exp_act = 48'hFFFFFFFFFFFF;
    endcase
  endfunction

  // Track valid past sample
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // 1-cycle latency functional correctness (both decoders)
  property p_decode_correct;
    @(posedge clk) disable iff (!past_valid)
      (device_out == exp_dev($past(probe0[15:0]))) &&
      (action_out == exp_act($past(probe1[47:0])));
  endproperty
  assert property (p_decode_correct);

  // Outputs constrained to legal value sets
  assert property (@(posedge clk)
    device_out inside {16'h0001,16'h0002,16'h0003,16'h0004,16'hFFFF});

  assert property (@(posedge clk)
    action_out inside {
      48'h000000000001,48'h000000000002,48'h000000000003,
      48'h000000000004,48'h000000000005,48'h000000000006,
      48'hFFFFFFFFFFFF});

  // No X/Z on outputs after first cycle
  assert property (@(posedge clk) disable iff (!past_valid)
    !$isunknown(device_out) && !$isunknown(action_out));

  // Functional coverage: hit each case arm (inputs sampled at prior cycle)
  cover property (@(posedge clk) disable iff (!past_valid) $past(probe0[15:0]) == 16'h0001);
  cover property (@(posedge clk) disable iff (!past_valid) $past(probe0[15:0]) == 16'h0002);
  cover property (@(posedge clk) disable iff (!past_valid) $past(probe0[15:0]) == 16'h0003);
  cover property (@(posedge clk) disable iff (!past_valid) $past(probe0[15:0]) == 16'h0004);
  cover property (@(posedge clk) disable iff (!past_valid)
    !($past(probe0[15:0]) inside {16'h0001,16'h0002,16'h0003,16'h0004})); // default

  cover property (@(posedge clk) disable iff (!past_valid) $past(probe1[47:0]) == 48'h000000000001);
  cover property (@(posedge clk) disable iff (!past_valid) $past(probe1[47:0]) == 48'h000000000002);
  cover property (@(posedge clk) disable iff (!past_valid) $past(probe1[47:0]) == 48'h000000000003);
  cover property (@(posedge clk) disable iff (!past_valid) $past(probe1[47:0]) == 48'h000000000004);
  cover property (@(posedge clk) disable iff (!past_valid) $past(probe1[47:0]) == 48'h000000000005);
  cover property (@(posedge clk) disable iff (!past_valid) $past(probe1[47:0]) == 48'h000000000006);
  cover property (@(posedge clk) disable iff (!past_valid)
    !($past(probe1[47:0]) inside {
      48'h000000000001,48'h000000000002,48'h000000000003,
      48'h000000000004,48'h000000000005,48'h000000000006})); // default

  // At least one cycle where both decoders take a recognized (non-default) value simultaneously
  cover property (@(posedge clk) disable iff (!past_valid)
    ($past(probe0[15:0]) inside {16'h0001,16'h0002,16'h0003,16'h0004}) &&
    ($past(probe1[47:0]) inside {
      48'h000000000001,48'h000000000002,48'h000000000003,
      48'h000000000004,48'h000000000005,48'h000000000006}));

endmodule

bind probe_decoder probe_decoder_sva
(
  .clk        (clk),
  .probe0     (probe0),
  .probe1     (probe1),
  .device_out (device_out),
  .action_out (action_out)
);