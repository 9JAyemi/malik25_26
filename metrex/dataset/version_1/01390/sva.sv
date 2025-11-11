// SVA for timer
module timer_sva #(parameter WIDTH=32, RANGE=60)
(
  input  logic                clk_normal,
  input  logic                clk_change_time,
  input  logic                power,
  input  logic                enable,
  input  logic                reset,
  input  logic                add_time,
  input  logic                sub_time,
  input  logic [WIDTH-1:0]    count,
  input  logic                sig_end
);

  // Recreate DUT clock select for assertion clocking
  logic true_clk_sva;
  assign true_clk_sva = (!power || reset || (!enable && (add_time || sub_time)))
                        ? clk_change_time : clk_normal;

  // basic parameter sanity
  initial begin
    assert (RANGE > 0) else $error("RANGE must be > 0");
    assert ((1<<WIDTH) >= RANGE) else $error("RANGE exceeds WIDTH capacity");
  end

  default clocking cb @(posedge true_clk_sva); endclocking

  // After first sampled edge, $past becomes valid
  bit init_done;
  initial init_done = 0;
  always @(posedge true_clk_sva) init_done <= 1'b1;

  // Environmental sanity
  assert property ( !(add_time && sub_time) )
    else $error("add_time and sub_time asserted together");

  // Count always within range
  assert property ( count < RANGE )
    else $error("count out of range");

  // Power-off clears
  assert property ( !power |-> (count == 0 && sig_end == 0) )
    else $error("Power-off must clear count/sig_end");

  // Reset clears count (sig_end is intentionally don't-care per RTL)
  assert property ( power && reset |-> count == 0 )
    else $error("Reset must clear count");

  // Idle holds state
  assert property ( disable iff (!init_done)
                    power && !reset && !enable && !add_time && !sub_time
                    |-> (count == $past(count) && sig_end == $past(sig_end)) )
    else $error("Idle state must hold");

  // Enabled counting: modulo increment and sig_end on wrap
  assert property ( disable iff (!init_done)
                    power && !reset && enable
                    |-> (count == (($past(count)+1)%RANGE) &&
                         sig_end == (count == 0)) )
    else $error("Enable path update/sig_end incorrect");

  // add_time when not enabled: modulo increment; sig_end unchanged
  assert property ( disable iff (!init_done)
                    power && !reset && !enable && add_time
                    |-> (count == (($past(count)+1)%RANGE) &&
                         sig_end == $past(sig_end)) )
    else $error("add_time path incorrect");

  // sub_time when not enabled: decrement with wrap; sig_end unchanged
  assert property ( disable iff (!init_done)
                    power && !reset && !enable && !add_time && sub_time
                    |-> ( ($past(count)==0) ? (count == RANGE-1)
                                            : (count == $past(count)-1) ) &&
                        (sig_end == $past(sig_end)) )
    else $error("sub_time path incorrect");

  // sig_end rise only on wrap from RANGE-1 under enable
  assert property ( disable iff (!init_done)
                    $rose(sig_end) |-> ($past(enable) && $past(count) == (RANGE-1) &&
                                        power && !reset) )
    else $error("sig_end should rise only on enabled wrap");

  // Clock selection checks vs behavior
  assert property ( power && !reset && enable |-> $rose(clk_normal) )
    else $error("Enabled counting must use clk_normal");

  assert property ( power && !reset && !enable && (add_time || sub_time)
                    |-> $rose(clk_change_time) )
    else $error("Time change must use clk_change_time");

  assert property ( power && !reset && !enable && !(add_time || sub_time)
                    |-> $rose(clk_normal) )
    else $error("Idle (powered) must use clk_normal");

  // true_clk edge must coincide with one of the source clocks
  assert property ( $rose(clk_normal) || $rose(clk_change_time) )
    else $error("true_clk edge without a source clock edge");

  // Coverage
  cover property ( power && !reset && enable && $past(count)==(RANGE-1) && count==0 && sig_end );
  cover property ( power && !reset && !enable && add_time && $past(count)==(RANGE-1) && count==0 );
  cover property ( power && !reset && !enable && !add_time && sub_time && $past(count)==0 && count==(RANGE-1) );
  cover property ( !power && count==0 && sig_end==0 );
  cover property ( power && !reset && !enable && !add_time && !sub_time [*2] );

endmodule

// Bind to DUT (assumes identical port names)
bind timer timer_sva #(.WIDTH(WIDTH), .RANGE(RANGE)) timer_sva_i (
  .clk_normal, .clk_change_time, .power, .enable, .reset, .add_time, .sub_time, .count, .sig_end
);