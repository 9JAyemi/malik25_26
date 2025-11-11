// Concise SVA checker for SPM
// Bind inside SPM scope to access internal signals (mem)
module SPM_sva;
  // Reuse DUT params
  localparam int DEPTH = depth;
  localparam int DW    = data_width;

  // Start checking after first clock
  bit init_done;
  always_ff @(posedge clk) init_done <= 1'b1;
  default clocking cb @(posedge clk); endclocking

  // Elaboration-time sanity: user clogb2 only matches $clog2 when DEPTH is power-of-two
  initial begin
    assert ($clog2(DEPTH) == clogb2(DEPTH))
      else $error("SPM: depth=%0d is not a power-of-two; clogb2 under-sizes addr", DEPTH);
  end

  // Inputs must be known when used
  assert property (cb (write_en || read_en) |-> !$isunknown({write_en, read_en, addr, data_in}));

  // Address must be within range whenever used
  assert property (cb (write_en || read_en) |-> (addr < DEPTH));

  // Write takes effect (observed next cycle)
  assert property (cb disable iff (!init_done)
                   $past(write_en) |-> (mem[$past(addr)] === $past(data_in)));

  // Read returns the memory value from before any same-cycle write (read-before-write)
  assert property (cb disable iff (!init_done)
                   read_en |-> (data_out === $past(mem[addr])));

  // data_out changes only on a read
  assert property (cb disable iff (!init_done)
                   $changed(data_out) |-> read_en);

  // When not reading, data_out holds its value
  assert property (cb disable iff (!init_done)
                   !read_en |-> $stable(data_out));

  // Coverage
  cover property (cb write_en);
  cover property (cb read_en);
  // Same-cycle read & write (single addr port => same address)
  cover property (cb write_en && read_en);
  // Write followed by read of same address next cycle
  cover property (cb $past(write_en) && read_en && (addr == $past(addr)));
  // Back-to-back writes to same address
  cover property (cb write_en ##1 write_en && (addr == $past(addr)));
  // Back-to-back reads (same addr) with no intervening write
  cover property (cb read_en ##1 read_en && (addr == $past(addr)));
endmodule

// Bind the checker into every SPM instance
bind SPM SPM_sva sva_i();