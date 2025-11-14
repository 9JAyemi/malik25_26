// SVA for ROM_A
// Bind this file alongside the DUT

module ROM_A_sva;
  // Access bound instance signals directly: addr, inst
  localparam int VALID_MAX = 66;

  // Expected ROM contents for indices [0:VALID_MAX]
  localparam logic [31:0] EXP_ROM [0:VALID_MAX] = '{
    32'h00000026, 32'h00210826, 32'h00421026, 32'h00631826,
    32'h00842026, 32'h00a52826, 32'h00c63026, 32'h00e73826,
    32'h01084026, 32'h01294826, 32'h014a5026, 32'h016b5826,
    32'h018c6026, 32'h01ad6826, 32'h01ce7026, 32'h01ef7826,
    32'h02108026, 32'h02318826, 32'h02529026, 32'h02739826,
    32'h0294a026, 32'h02b5a826, 32'h02d6b026, 32'h02f7b826,
    32'h0318c026, 32'h0339c826, 32'h035ad026, 32'h037bd826,
    32'h039ce026, 32'h03bde826, 32'h03def026, 32'h03fff826,
    32'h2108000a, 32'h21290001, 32'h214a0002, 32'h216b0003,
    32'h218c0004, 32'h21ad000a, 32'h21ce000a, 32'h21ef000a,
    32'h00892020, 32'h00aa2820, 32'h00cb3020, 32'h00ec3820,
    32'h1488fffb, 32'h22100001, 32'h3c088000, 32'h00008827,
    32'h00084042, 32'h02119024, 32'h01119825, 32'h0111a026,
    32'h1408fffb, 32'h3c1500ff, 32'h22b500ff, 32'hac150320,
    32'h8c160320, 32'h12b60000, 32'h00892022, 32'h00aa2822,
    32'h00cb3022, 32'h00ec3822, 32'h00c0402a, 32'h1008fffa,
    32'h0c000042, 32'h08000000, 32'h03e00008
  };

  bit init_done;
  initial begin
    #0 init_done = 1'b1; // start checking after time-0 init completes
  end

  // No X/Z on address
  a_no_x_addr: assert property (@(addr)
    disable iff (!init_done)
    !$isunknown(addr)
  );

  // Address within implemented range [0:VALID_MAX]
  a_addr_in_range: assert property (@(addr)
    disable iff (!init_done)
    $unsigned(addr) <= VALID_MAX
  );

  // For valid addr, inst is known and equals expected in zero time (combinational)
  a_data_match: assert property (@(addr or inst)
    disable iff (!init_done)
    (!$isunknown(addr) && ($unsigned(addr) <= VALID_MAX))
      |-> ##0 ( ! $isunknown(inst) && inst == EXP_ROM[$unsigned(addr)] )
  );

  // If addr stable, inst must hold (glitch-free with stable addr)
  a_hold_when_addr_stable: assert property (@(addr or inst)
    disable iff (!init_done)
    $stable(addr) |-> ##0 $stable(inst)
  );

  // If addr is X/Z or out of valid range, inst must be X (tools typically drive X on OOB)
  a_x_when_bad_addr: assert property (@(addr)
    disable iff (!init_done)
    ( $isunknown(addr) || ($unsigned(addr) > VALID_MAX) )
      |-> ##0 $isunknown(inst)
  );

  // Functional coverage: hit every valid address and value at least once
  genvar i;
  generate
    for (i = 0; i <= VALID_MAX; i++) begin : COV
      c_addr_i: cover property (@(addr)
        disable iff (!init_done)
        !$isunknown(addr) && ($unsigned(addr) == i)
      );
      c_inst_i: cover property (@(inst)
        disable iff (!init_done)
        inst == EXP_ROM[i]
      );
    end
  endgenerate
endmodule

bind ROM_A ROM_A_sva u_ROM_A_sva();