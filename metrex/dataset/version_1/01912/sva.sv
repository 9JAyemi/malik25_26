// SVA checker for synth_ram. Bind this to the DUT.
// Focus: read-first semantics, byte-write masking, enable gating, addr range, and functional coverage.

module synth_ram_sva #(parameter int WORDS = 64)
(
  input logic        clk,
  input logic        ena,
  input logic [3:0]  wen,
  input logic [21:0] addr,
  input logic [31:0] wdata,
  input logic [31:0] rdata
);
  bit                 initialized;
  bit [31:0]          model_mem [0:WORDS-1];
  bit [31:0]          exp_rdata;

  // Simple reference model with read-first behavior and byte masking
  always_ff @(posedge clk) begin
    if (!initialized) begin
      initialized <= 1'b1;
      exp_rdata   <= 'x;
      for (int i = 0; i < WORDS; i++) model_mem[i] <= 'x;
    end else begin
      int unsigned a = addr;
      bit [31:0] exp_next = exp_rdata;

      if (ena && (a < WORDS)) begin
        // read-first: rdata gets old contents
        exp_next = model_mem[a];

        // masked write to memory
        bit [31:0] new_word = model_mem[a];
        if (wen[0]) new_word[ 7: 0] = wdata[ 7: 0];
        if (wen[1]) new_word[15: 8] = wdata[15: 8];
        if (wen[2]) new_word[23:16] = wdata[23:16];
        if (wen[3]) new_word[31:24] = wdata[31:24];
        model_mem[a] = new_word;
      end

      exp_rdata <= exp_next;

      // Golden check: rdata must match the reference model
      assert (rdata === exp_next)
        else $error("synth_ram SVA: rdata mismatch exp=%h got=%h addr=%0d wen=%b ena=%0b",
                    exp_next, rdata, addr, wen, ena);
    end
  end

  // rdata may only change in cycles when ena is 1
  property p_rdata_only_changes_when_ena;
    @(posedge clk) disable iff (!initialized)
      $changed(rdata) |-> ena;
  endproperty
  assert property (p_rdata_only_changes_when_ena);

  // Address must be in range whenever enabled
  property p_addr_in_range_when_ena;
    @(posedge clk) disable iff (!initialized)
      ena |-> (addr < WORDS);
  endproperty
  assert property (p_addr_in_range_when_ena);

  // When enabled, control/data must be known (prevents X-driven undefined behavior)
  property p_no_x_on_inputs_when_ena;
    @(posedge clk) disable iff (!initialized)
      ena |-> !$isunknown({wen, addr, wdata});
  endproperty
  assert property (p_no_x_on_inputs_when_ena);

  // Functional coverage
  // Read (no write)
  cover property (@(posedge clk) initialized && ena && (wen == 4'b0000));
  // Single-byte writes
  cover property (@(posedge clk) initialized && ena && (wen == 4'b0001));
  cover property (@(posedge clk) initialized && ena && (wen == 4'b0010));
  cover property (@(posedge clk) initialized && ena && (wen == 4'b0100));
  cover property (@(posedge clk) initialized && ena && (wen == 4'b1000));
  // Multi-byte writes and full word write
  cover property (@(posedge clk) initialized && ena && (wen == 4'b0011));
  cover property (@(posedge clk) initialized && ena && (wen == 4'b1100));
  cover property (@(posedge clk) initialized && ena && (wen == 4'b1111));
  // Back-to-back writes to same address
  cover property (@(posedge clk) initialized
                  (ena && wen!=0) ##1 (ena && wen!=0 && addr==$past(addr)));
  // Write then read same address (read-first visible on write cycle, then new data visible on subsequent read)
  cover property (@(posedge clk) initialized
                  (ena && wen!=0) ##1 (ena && wen==0 && addr==$past(addr)));

endmodule

// Bind into the DUT
bind synth_ram synth_ram_sva #(.WORDS(WORDS)) synth_ram_sva_i (
  .clk   (clk),
  .ena   (ena),
  .wen   (wen),
  .addr  (addr),
  .wdata (wdata),
  .rdata (rdata)
);