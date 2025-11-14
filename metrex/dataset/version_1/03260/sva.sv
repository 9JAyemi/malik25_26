// SVA for KeyBoardController
// Bindable assertion module focusing on key behaviors, with multi-clock checks.

module KeyBoardController_asserts (
  input  logic        clk,
  input  logic        PS2C,
  input  logic        PS2D,
  input  logic        InteAccept,
  input  logic [15:0] scanCode,
  input  logic        KeyBoardInte,

  input  logic [7:0]  ps2c_filter,
  input  logic [7:0]  ps2d_filter,
  input  logic        PS2Cf,
  input  logic        PS2Df,

  input  logic [22:0] count,
  input  logic [3:0]  put,
  input  logic [3:0]  get,
  input  logic [3:0]  state,
  input  logic [10:0] shift1,
  input  logic [10:0] shift2,
  input  logic        new_flag,

  input  logic        rst
);

  // past-valid guards
  logic past_clk, past_ps2;
  initial begin past_clk = 1'b0; past_ps2 = 1'b0; end
  always @(posedge clk) past_clk <= 1'b1;
  always @(negedge PS2Cf or posedge rst) if (rst) past_ps2 <= 1'b0; else past_ps2 <= 1'b1;

  // Default clocking blocks
  default clocking cb_clk @(posedge clk); endclocking
  clocking cb_ps2 @(negedge PS2Cf); endclocking

  // 1) PS2 input filtering behavior
  // PS2Cf/PS2Df set on all-1s, clear on all-0s, otherwise hold last value
  property p_ps2c_set1;  @(cb_clk) ps2c_filter == 8'hFF |-> ##1 PS2Cf; endproperty
  property p_ps2c_set0;  @(cb_clk) ps2c_filter == 8'h00 |-> ##1 !PS2Cf; endproperty
  property p_ps2c_hold;  @(cb_clk) (ps2c_filter != 8'hFF && ps2c_filter != 8'h00 && past_clk) |-> ##1 PS2Cf == $past(PS2Cf); endproperty
  property p_ps2d_set1;  @(cb_clk) ps2d_filter == 8'hFF |-> ##1 PS2Df; endproperty
  property p_ps2d_set0;  @(cb_clk) ps2d_filter == 8'h00 |-> ##1 !PS2Df; endproperty
  property p_ps2d_hold;  @(cb_clk) (ps2d_filter != 8'hFF && ps2d_filter != 8'h00 && past_clk) |-> ##1 PS2Df == $past(PS2Df); endproperty

  assert property(p_ps2c_set1);
  assert property(p_ps2c_set0);
  assert property(p_ps2c_hold);
  assert property(p_ps2d_set1);
  assert property(p_ps2d_set0);
  assert property(p_ps2d_hold);

  // 2) Count/rst behavior
  property p_count_inc;   @(cb_clk) past_clk && PS2Df |-> count == $past(count) + 23'd1; endproperty
  property p_count_rst;   @(cb_clk) !PS2Df |-> count == 23'd1; endproperty
  property p_rst_def;     @(cb_clk) rst == (count == 23'd0); endproperty

  assert property(p_count_inc);
  assert property(p_count_rst);
  assert property(p_rst_def);

  // 3) PS/2 state machine (negedge PS2Cf domain)
  // Legal range and transition (0..10; +1 each clock; wrap 10->0; async reset)
  property p_state_range;   @(cb_ps2) state <= 4'd10; endproperty
  property p_state_trans;   @(cb_ps2) disable iff (rst) past_ps2 |-> ( $past(state)==4'd10 ? state==4'd0 : state==$past(state)+4'd1 ); endproperty

  assert property(p_state_range);
  assert property(p_state_trans);

  // 4) Shift registers behavior (sampled on negedge PS2Cf)
  property p_shift1;  @(cb_ps2) disable iff (rst) shift1 == {PS2Df, $past(shift1[10:1])}; endproperty
  property p_shift2;  @(cb_ps2) disable iff (rst) shift2 == {$past(shift1[0]), $past(shift2[10:1])}; endproperty

  assert property(p_shift1);
  assert property(p_shift2);

  // 5) 'new' flag and buffer push/pointer control (clk domain)
  // new asserted when state==10 is observed in clk domain
  property p_new_set;       @(cb_clk) state==4'd10 |-> ##1 new_flag; endproperty
  // push occurs only when (state==0 && new && space); then new clears and put increments by 1 (mod 16)
  property p_push_effect;   @(cb_clk) past_clk && (state==4'd0 && new_flag && (put != get - 4'd1)) |-> ##1 (!new_flag && put == $past(put)+4'd1); endproperty
  // no push when full (put==get-1)
  property p_no_push_full;  @(cb_clk) (state==4'd0 && new_flag && (put == get - 4'd1)) |-> ##1 (put==$past(put) && new_flag); endproperty
  // put changes only due to the push condition
  property p_put_stable;    @(cb_clk) past_clk && !(state==4'd0 && new_flag && (put != get - 4'd1)) |-> ##1 put == $past(put); endproperty

  assert property(p_new_set);
  assert property(p_push_effect);
  assert property(p_no_push_full);
  assert property(p_put_stable);

  // 6) Get pointer and interrupt behavior (clk domain)
  // Pop on InteAccept when not empty; IRQ deasserts on same cycle; get increments by 1
  property p_accept_pop;    @(cb_clk) past_clk && (InteAccept && (get != put)) |-> ##1 (get == $past(get)+4'd1 && !KeyBoardInte); endproperty
  // get changes only on valid accept
  property p_get_stable;    @(cb_clk) past_clk && !(InteAccept && (get != put)) |-> ##1 get == $past(get); endproperty

  assert property(p_accept_pop);
  assert property(p_get_stable);

  // Interrupt only raises when there is data, holds while pending, and falls only on accept or empty
  property p_irq_rise_when_nonempty; @(cb_clk) $rose(KeyBoardInte) |-> $past(get != put); endproperty
  property p_irq_hold;               @(cb_clk) KeyBoardInte && !InteAccept && (get != put) |-> ##1 KeyBoardInte; endproperty
  property p_irq_fall_reason;        @(cb_clk) $fell(KeyBoardInte) |-> ($past(InteAccept) || $past(get==put)); endproperty
  property p_empty_clears_irq;       @(cb_clk) (get == put) |-> ##1 !KeyBoardInte; endproperty

  assert property(p_irq_rise_when_nonempty);
  assert property(p_irq_hold);
  assert property(p_irq_fall_reason);
  assert property(p_empty_clears_irq);

  // 7) Key coverage
  // a) Full PS/2 frame (0->10->0) in PS2 domain
  cover property (@(cb_ps2) disable iff (rst)
                  (state==4'd0) ##1 (state==4'd1) ##1 (state==4'd2) ##1 (state==4'd3) ##1
                  (state==4'd4) ##1 (state==4'd5) ##1 (state==4'd6) ##1 (state==4'd7) ##1
                  (state==4'd8) ##1 (state==4'd9) ##1 (state==4'd10) ##1 (state==4'd0));

  // b) new set then pushed into buffer (space available)
  cover property (@(cb_clk) (state==4'd10) ##1 new_flag ##[1:10] (state==4'd0 && new_flag && (put != get - 4'd1)) ##1 !new_flag);

  // c) Interrupt handshake: raise then accept and drop
  cover property (@(cb_clk) $rose(KeyBoardInte) ##[1:8] (InteAccept && $fell(KeyBoardInte)));

  // d) Pointer wrap-around on put and get
  cover property (@(cb_clk) (state==4'd0 && new_flag && (put != get - 4'd1) && put==4'hF) ##1 (put==4'h0));
  cover property (@(cb_clk) (InteAccept && (get != put) && get==4'hF) ##1 (get==4'h0));

  // e) Full condition observed (no push)
  cover property (@(cb_clk) (state==4'd0 && new_flag && (put == get - 4'd1)));

  // f) Inactivity reset observed
  cover property (@(cb_clk) rst);

endmodule

// Bind into DUT
bind KeyBoardController KeyBoardController_asserts sva (
  .clk(clk),
  .PS2C(PS2C),
  .PS2D(PS2D),
  .InteAccept(InteAccept),
  .scanCode(scanCode),
  .KeyBoardInte(KeyBoardInte),

  .ps2c_filter(ps2c_filter),
  .ps2d_filter(ps2d_filter),
  .PS2Cf(PS2Cf),
  .PS2Df(PS2Df),

  .count(count),
  .put(put),
  .get(get),
  .state(state),
  .shift1(shift1),
  .shift2(shift2),
  .new_flag(new),
  .rst(rst)
);