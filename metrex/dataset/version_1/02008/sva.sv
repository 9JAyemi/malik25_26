// SVA for module square
module square_sva (
  input  logic                 clksamp,
  input  logic [31:0]          freq,
  input  logic signed [16:0]   amp,
  input  logic signed [16:0]   offset,
  input  logic [9:0]           duty,
  input  logic [11:0]          sq,

  // internal DUT signals
  input  logic                 state,
  input  logic [15:0]          period_counter,
  input  logic [15:0]          duty_counter,
  input  logic [15:0]          period_load,
  input  logic [15:0]          duty_load,
  input  logic [15:0]          period_load_reg,
  input  logic [15:0]          duty_load_reg
);

  // past-valid gate (no explicit reset in DUT)
  bit past_valid;
  initial past_valid = 0;
  always @(posedge clksamp) past_valid <= 1'b1;

  // helpers
  function automatic logic [11:0] clip12_signed(input logic signed [17:0] v);
    if (v > 18'sd4095) clip12_signed = 12'd4095;
    else if (v < 0)    clip12_signed = 12'd0;
    else               clip12_signed = v[11:0];
  endfunction

  function automatic logic [11:0] upper_clip_offset(input logic signed [16:0] o);
    if (o > 17'sd4095) upper_clip_offset = 12'd4095;
    else               upper_clip_offset = o[11:0]; // truncation matches DUT
  endfunction

  function automatic logic [15:0] duty_calc(input logic [15:0] pl, input logic [9:0] d);
    duty_calc = ((pl * d) / 10'd1000)[15:0];
  endfunction

  // 1) Registering of load values
  assert property (@(posedge clksamp) past_valid |-> period_load_reg == $past(period_load));
  assert property (@(posedge clksamp) past_valid |-> duty_load_reg   == $past(duty_load));

  // 2) period_counter next-state behavior
  assert property (@(posedge clksamp) past_valid |-> 
    ($past(period_load_reg) != $past(period_load)) ? (period_counter == $past(period_load_reg) - 16'd1) :
    ($past(period_counter)  >  16'd0)              ? (period_counter == $past(period_counter)  - 16'd1) :
                                                     (period_counter == $past(period_load_reg) - 16'd1));

  // 3) duty_counter next-state behavior
  assert property (@(posedge clksamp) past_valid |-> 
    ($past(duty_load_reg) != $past(duty_load))     ? (duty_counter == $past(duty_load_reg) - 16'd1) :
    ($past(duty_counter)  >  16'd0)                ? (duty_counter == $past(duty_counter)  - 16'd1) :
    ($past(period_counter) >  16'd0)               ? (duty_counter == 16'd0) :
                                                     (duty_counter == $past(duty_load_reg) - 16'd1));

  // 4) state next-state behavior
  assert property (@(posedge clksamp) past_valid |-> 
    state == (($past(duty_counter) == 16'd0 && $past(period_counter) > 16'd0) ? 1'b0 : 1'b1));

  // 5) duty_load arithmetic
  assert property (@(posedge clksamp) past_valid |-> duty_load == duty_calc(period_load, duty));

  // 6) Output sq functional behavior (matches DUT precedence and clipping)
  // DC path: freq==0 or amp==0
  assert property (@(posedge clksamp)
    (freq == 32'd0 || amp == 17'sd0) |-> (sq == upper_clip_offset(offset)));

  // duty==0 path (when not DC)
  assert property (@(posedge clksamp)
    (freq != 32'd0 && amp != 17'sd0 && duty == 10'd0) |-> (sq == 12'd0));

  // normal square path with saturation
  assert property (@(posedge clksamp)
    (freq != 32'd0 && amp != 17'sd0 && duty != 10'd0) |->
      (sq == clip12_signed(state ? (offset + amp) : (offset - amp))));

  // 7) Range/sanity
  assert property (@(posedge clksamp) sq <= 12'd4095);

  // 8) Useful covers
  cover property (@(posedge clksamp) past_valid && ($past(period_counter)==16'd0) ##1 (period_counter == $past(period_load_reg)-16'd1));
  cover property (@(posedge clksamp) past_valid && ($past(duty_counter)==16'd0) && ($past(period_counter)>0) ##1 (duty_counter==16'd0) && (state==1'b0));
  cover property (@(posedge clksamp) (freq!=0 && amp!=0 && duty!=0) &&
                                    (state ? (offset + amp) : (offset - amp)) > 18'sd4095 && (sq==12'd4095));
  cover property (@(posedge clksamp) (freq!=0 && amp!=0 && duty!=0) &&
                                    (state ? (offset + amp) : (offset - amp)) < 0 && (sq==12'd0));
  cover property (@(posedge clksamp) (freq==0) && (offset < 0) && (sq == upper_clip_offset(offset)));

endmodule

// Bind to all instances of square
bind square square_sva sva_square (.*);