// SVA checker for four_input_signed_adder
// Concise, end-to-end correctness and latency checks + focused coverage.
module four_input_signed_adder_sva #(
  parameter int DELAY_DATA_WIDTH = 16
)(
  input  logic                     clk,
  input  logic [24:0]              data_1,
  input  logic [24:0]              data_2,
  input  logic [24:0]              data_3,
  input  logic [24:0]              data_4,
  input  logic [7:0]               data_p,
  input  logic [DELAY_DATA_WIDTH-1:0] ddata_in,
  input  logic [DELAY_DATA_WIDTH-1:0] ddata_out
);

  // Helper: absolute-value transform used by DUT (per the two’s complement logic in stage 1)
  function automatic logic [24:0] abs25 (input logic [24:0] x);
    abs25 = x[24] ? (~{1'b0, x[23:0]} + 25'd1) : {1'b0, x[23:0]};
  endfunction

  // Helper: truncate to 25b (DUT adders are 25b wide, i.e. modulo 2^25)
  function automatic logic [24:0] trunc25 (input logic [26:0] x);
    trunc25 = x[24:0];
  endfunction

  // Helper: saturation mapping used by DUT output stage
  function automatic logic [7:0] sat8_from25 (input logic [24:0] s);
    if (s[24])                  sat8_from25 = 8'h00;
    else if (s[23:20] == 4'd0)  sat8_from25 = s[19:12];
    else                        sat8_from25 = 8'hFF;
  endfunction

  // Expected sum and output from inputs (modulo-25b arithmetic, 4-cycle latency to data_p)
  function automatic logic [24:0] exp_sum25 (
    input logic [24:0] a, b, c, d
  );
    logic [26:0] full;
    full      = abs25(a) + abs25(b) + abs25(c) + abs25(d);
    exp_sum25 = trunc25(full);
  endfunction

  function automatic logic [7:0] exp_data_p (
    input logic [24:0] a, b, c, d
  );
    exp_data_p = sat8_from25(exp_sum25(a,b,c,d));
  endfunction

  // History guard to safely use $past(...,4)
  logic [2:0] hist_cnt;
  logic       hist_ok;
  always_ff @(posedge clk) begin
    if (hist_cnt != 3'd4) hist_cnt <= hist_cnt + 3'd1;
    hist_ok <= (hist_cnt >= 3'd4);
  end

  // 1) Pass-through latency check for ddata path (exactly 4 cycles)
  property p_ddata_latency;
    @(posedge clk) hist_ok |-> ddata_out == $past(ddata_in,4);
  endproperty
  assert property (p_ddata_latency);

  // 2) End-to-end functional check for data_p (abs -> sum mod 2^25 -> saturate), 4-cycle latency
  property p_data_p_functional;
    @(posedge clk) hist_ok |-> data_p == exp_data_p($past(data_1,4), $past(data_2,4),
                                                    $past(data_3,4), $past(data_4,4));
  endproperty
  assert property (p_data_p_functional);

  // 3) No-X on outputs once history is valid
  property p_no_x_outputs;
    @(posedge clk) hist_ok |-> !$isunknown({data_p, ddata_out});
  endproperty
  assert property (p_no_x_outputs);

  // Coverage: exercise all output behaviors and latency
  // a) Negative (wrapped) sum -> saturate to 0x00
  cover property (@(posedge clk)
    hist_ok && (sat8_from25(exp_sum25($past(data_1,4),$past(data_2,4),
                                      $past(data_3,4),$past(data_4,4))) == 8'h00));

  // b) In-range -> true 8-bit value (1..254)
  cover property (@(posedge clk)
    hist_ok && (sat8_from25(exp_sum25($past(data_1,4),$past(data_2,4),
                                      $past(data_3,4),$past(data_4,4))) inside {[8'h01:8'hFE]}));

  // c) Overflow high -> saturate to 0xFF
  cover property (@(posedge clk)
    hist_ok && (sat8_from25(exp_sum25($past(data_1,4),$past(data_2,4),
                                      $past(data_3,4),$past(data_4,4))) == 8'hFF));

  // d) ddata latency observable (change propagates in exactly 4 cycles)
  cover property (@(posedge clk)
    $changed(ddata_in) |-> ##4 (ddata_out == $past(ddata_in,4) && $changed(ddata_out)));

endmodule

// Bind into DUT
bind four_input_signed_adder
  four_input_signed_adder_sva #(.DELAY_DATA_WIDTH(DELAY_DATA_WIDTH))
    four_input_signed_adder_sva_i (.*);