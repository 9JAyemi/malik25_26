// SVA for RAM_SHIFTER
// Bind this module to the DUT to check behavior and cover key scenarios.

module RAM_SHIFTER_sva #(
  parameter int IO_WIDTH   = 16,
  parameter int ADDR_WIDTH = 4,
  parameter int PHASE_SHIFT= 2
) ();

  // Parameter sanity (prevents out-of-range indexing)
  initial begin
    assert (IO_WIDTH >= 2)
      else $error("RAM_SHIFTER: IO_WIDTH must be >= 2");
    assert (PHASE_SHIFT > 0 && PHASE_SHIFT < IO_WIDTH)
      else $error("RAM_SHIFTER: PHASE_SHIFT must be in 1..IO_WIDTH-1");
  end

  default clocking cb @(posedge clk); endclocking

  // Start checks after first clock to avoid $past at time 0
  logic started;
  always_ff @(posedge clk) started <= 1'b1;
  default disable iff (!started);

  // Continuous connection check
  assert property (ram_in == shift_in[0]);

  // Address increments by 1 modulo 2^ADDR_WIDTH
  assert property (addr == $past(addr,1,'0) + 1);

  // shift_out shifts in ram_out every cycle
  assert property (
    shift_out == { $past(shift_out,1,'0)[IO_WIDTH-2:0], $past(ram_out,1,'0) }
  );

  // shift_in capture/rotate behavior
  assert property (
    ($past(addr,1,'0) == '0) |-> (shift_in == $past(in,1,'0))
  );
  assert property (
    ($past(addr,1,'0) != '0) |-> (shift_in == { $past(shift_in,1,'0)[IO_WIDTH-2:0],
                                                $past(shift_in,1,'0)[IO_WIDTH-1] })
  );

  // out updates only when addr == 0
  assert property (
    ($past(addr,1,'0) != '0) |-> (out == $past(out,1,'0))
  );

  // out is rotate-left(PHASE_SHIFT) of prior shift_out when addr == 0
  assert property (
    ($past(addr,1,'0) == '0) |-> (out ==
      { $past(shift_out,1,'0)[IO_WIDTH-PHASE_SHIFT-1:0],
        $past(shift_out,1,'0)[IO_WIDTH-1:IO_WIDTH-PHASE_SHIFT] })
  );

  // Coverage

  // Address wrap
  cover property ($past(addr) == {ADDR_WIDTH{1'b1}} && addr == '0);

  // Branch coverage (addr==0 update)
  cover property (
    ($past(addr) == '0) &&
    (out == { $past(shift_out)[IO_WIDTH-PHASE_SHIFT-1:0],
              $past(shift_out)[IO_WIDTH-1:IO_WIDTH-PHASE_SHIFT] })
  );

  // Branch coverage (addr!=0 rotate path)
  cover property (
    ($past(addr) != '0) &&
    (shift_in == { $past(shift_in)[IO_WIDTH-2:0], $past(shift_in)[IO_WIDTH-1] })
  );

  // Observe both ram_in polarities
  cover property (ram_in == 0);
  cover property (ram_in == 1);

endmodule

// Bind into the DUT
bind RAM_SHIFTER RAM_SHIFTER_sva #(
  .IO_WIDTH(IO_WIDTH),
  .ADDR_WIDTH(ADDR_WIDTH),
  .PHASE_SHIFT(PHASE_SHIFT)
) RAM_SHIFTER_sva_i();