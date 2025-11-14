// SVA checker for dual_port_ram
// Focus: data integrity, enables, X-checks, read-hold, RAW behavior, concise coverage
module dual_port_ram_sva
  #(parameter DW=8, AW=6, DEPTH=1<<AW)
  (input wrclk,
   input [DW-1:0] di,
   input wren,
   input [AW-1:0] wraddr,
   input rdclk,
   input rden,
   input [AW-1:0] rdaddr,
   input [DW-1:0] do);

  // Lightweight reference model (scoreboard) with known-value mask
  logic [DW-1:0] ref_mem [0:DEPTH-1];
  bit            has_val [0:DEPTH-1];

  // Initialize only addresses explicitly initialized in DUT
  initial begin
    foreach (has_val[i]) has_val[i] = 1'b0;
    ref_mem[0] = 8'h01; has_val[0] = 1;
    ref_mem[1] = 8'hAA; has_val[1] = 1;
    ref_mem[2] = 8'h55; has_val[2] = 1;
    ref_mem[3] = 8'hFF; has_val[3] = 1;
    ref_mem[4] = 8'hF0; has_val[4] = 1;
    ref_mem[5] = 8'h0F; has_val[5] = 1;
    ref_mem[6] = 8'hCC; has_val[6] = 1;
    ref_mem[7] = 8'h33; has_val[7] = 1;
    ref_mem[8] = 8'h02; has_val[8] = 1;
    ref_mem[9] = 8'h04; has_val[9] = 1;
  end

  // Mirror writes
  always_ff @(posedge wrclk) begin
    assert (!$isunknown(wren)) else $error("wren is X/Z at wrclk");
    if (wren && !$isunknown({wraddr, di})) begin
      ref_mem[wraddr] = di;   // blocking to reflect same-time visibility
      has_val[wraddr] = 1'b1;
    end
  end

  // Read checks (registered, synchronous read)
  always_ff @(posedge rdclk) begin
    assert (!$isunknown(rden)) else $error("rden is X/Z at rdclk");

    // Output should hold when rden==0
    if (!rden) begin
      assert (do == $past(do)) else
        $error("do changed without read enable");
    end

    // On valid read, data must match reference
    if (rden && !$isunknown(rdaddr)) begin
      bit coincident_wr  = $rose(wrclk);
      bit same_addr      = (wraddr == rdaddr) && !$isunknown(wraddr);
      bit coincident_haz = coincident_wr && wren && same_addr && !$isunknown(di);

      // Allow either old or new data on exact coincident read-during-write to same addr
      if (has_val[rdaddr]) begin
        if (coincident_haz)
          assert (do == ref_mem[rdaddr] || do == di) else
            $error("Read-during-write same-edge mismatch: addr=%0d exp_old=%0h exp_new=%0h got=%0h",
                   rdaddr, ref_mem[rdaddr], di, do);
        else
          assert (do == ref_mem[rdaddr]) else
            $error("Read data mismatch: addr=%0d exp=%0h got=%0h", rdaddr, ref_mem[rdaddr], do);
      end

      // Data must be known on valid read of known location
      if (has_val[rdaddr]) begin
        assert (!$isunknown(do)) else $error("do is X/Z on valid read");
      end
    end
  end

  // X-checks on used inputs
  property p_no_x_on_write_inputs;
    @(posedge wrclk) wren |-> !$isunknown({wraddr, di});
  endproperty
  assert property (p_no_x_on_write_inputs) else
    $error("wraddr/di X/Z when wren=1");

  property p_no_x_on_read_addr;
    @(posedge rdclk) rden |-> !$isunknown(rdaddr);
  endproperty
  assert property (p_no_x_on_read_addr) else
    $error("rdaddr X/Z when rden=1");

  // Coverage
  // Basic enables
  cover property (@(posedge wrclk) wren);
  cover property (@(posedge rdclk) rden);

  // Read known, pre-initialized locations
  cover property (@(posedge rdclk) rden && rdaddr==6'd0 && do==8'h01);
  cover property (@(posedge rdclk) rden && rdaddr==6'd3 && do==8'hFF);
  cover property (@(posedge rdclk) rden && rdaddr==6'd6 && do==8'hCC);

  // Write lowest and highest addresses
  cover property (@(posedge wrclk) wren && wraddr==6'd0);
  cover property (@(posedge wrclk) wren && wraddr==6'd63);

  // Read-after-write same address observed (within a window)
  property cov_read_after_write;
    logic [AW-1:0] a; logic [DW-1:0] d;
    @(posedge wrclk) (wren && !$isunknown({wraddr,di}), a=wraddr, d=di)
    ##[1:20] @(posedge rdclk) (rden && rdaddr==a && do==d);
  endproperty
  cover property (cov_read_after_write);

  // Read hold (rden=0) observed
  cover property (@(posedge rdclk) !rden && $past(!rden) && do==$past(do));
endmodule

// Bind into the DUT
bind dual_port_ram dual_port_ram_sva #(.DW(8), .AW(6), .DEPTH(64)) dual_port_ram_sva_i
(
  .wrclk(wrclk),
  .di(di),
  .wren(wren),
  .wraddr(wraddr),
  .rdclk(rdclk),
  .rden(rden),
  .rdaddr(rdaddr),
  .do(do)
);