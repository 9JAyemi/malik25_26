// SVA for shift_reg_LED
module shift_reg_LED_sva (
  input logic         clk,
  input logic [7:0]   data,
  input logic [2:0]   LED,
  input logic [7:0]   shift_reg,
  input logic [2:0]   counter
);
  default clocking cb @(posedge clk); endclocking

  // Static sanity: concatenation width must match destination (will flag current bug)
  initial begin
    assert ($bits({shift_reg[6:0], data}) == $bits(shift_reg))
      else $error("Width mismatch: {%0d} assigned to %0d-bit shift_reg",
                  $bits({shift_reg[6:0], data}), $bits(shift_reg));
  end

  // No X/Z after init
  assert property (disable iff ($initstate) !$isunknown({counter, shift_reg, LED}));

  // Counter: +1 modulo 8 each cycle
  assert property (disable iff ($initstate)
                   !$isunknown($past(counter)) |->
                   counter == (($past(counter)==3'd7) ? 3'd0 : $past(counter)+3'd1));

  // Shift register next value (exposes that current RTL truncates to data)
  assert property (disable iff ($initstate)
                   !$isunknown($past(data)) |->
                   shift_reg == $past(data));

  // LED updates only on wrap
  assert property (disable iff ($initstate)
                   !$isunknown($past(LED)) |->
                   (LED != $past(LED)) |-> ($past(counter)==3'd7));

  // LED value on wrap is from prior shift_reg bits
  assert property (disable iff ($initstate)
                   $past(counter)==3'd7 |-> LED == {$past(shift_reg)[7],
                                                    $past(shift_reg)[3],
                                                    $past(shift_reg)[0]});

  // LED holds otherwise
  assert property (disable iff ($initstate)
                   $past(counter)!=3'd7 |-> LED == $past(LED));

  // Coverage
  cover property (counter==3'd7);
  cover property ($past(counter)==3'd7 &&
                  LED == {$past(shift_reg)[7], $past(shift_reg)[3], $past(shift_reg)[0]});
  cover property (LED != $past(LED));
endmodule

// Bind into DUT (accesses internal regs shift_reg and counter)
bind shift_reg_LED shift_reg_LED_sva
  (.clk(clk), .data(data), .LED(LED), .shift_reg(shift_reg), .counter(counter));