// SVA for baud_rate_generator
module baud_rate_generator_sva #(
  parameter int unsigned BAUD_RATE = 9600,
  parameter int unsigned freq      = 16000000
)(
  input  logic        clk,
  input  logic        rst_n,
  input  logic        bps_start,
  input  logic        clk_baud,
  input  logic [31:0] counter,
  input  logic        toggle
);

  localparam int unsigned DIV = freq / (BAUD_RATE*2);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Basic parameter sanity
  initial begin
    assert (BAUD_RATE > 0 && freq > 0)
      else $error("Invalid parameters: BAUD_RATE=%0d freq=%0d", BAUD_RATE, freq);
  end

  // Async reset clears regs
  assert property (@(posedge clk) !rst_n |-> (counter == 32'd0 && toggle == 1'b0));

  // Output mapping
  assert property (clk_baud == toggle);

  // Hold when not counting
  assert property (!bps_start |-> ($stable(counter) && $stable(toggle)));

  // Counter increments when running and not at DIV
  assert property (bps_start && counter != DIV |=> counter == $past(counter) + 1);

  // Rollover and toggle at DIV
  assert property (bps_start && counter == DIV |=> (counter == 32'd0 && toggle != $past(toggle)));

  // Toggle occurs only due to rollover while running
  assert property ((toggle != $past(toggle)) |-> ($past(bps_start) && $past(counter) == DIV));

  // Counter never exceeds DIV (effective next-state semantics)
  assert property (counter <= DIV);

  // Knownness after reset release
  assert property (!$isunknown({counter, toggle, clk_baud}));

  // Coverage
  cover property (bps_start && counter == DIV);                            // hit terminal count
  cover property (bps_start && (toggle != $past(toggle)));                 // any toggle
  cover property (bps_start && (toggle != $past(toggle))
                  ##1 bps_start[*DIV] ##1 bps_start && (toggle != $past(toggle))); // two toggles spaced by DIV+1 cycles
  cover property ($rose(bps_start) ##1 !bps_start[*3] ##1 $rose(bps_start)); // start/stop/start
  cover property (!rst_n ##1 rst_n ##1 (counter == 0 && toggle == 0));     // reset behavior

endmodule

// Example bind (connects to internal regs)
bind baud_rate_generator
  baud_rate_generator_sva #(.BAUD_RATE(BAUD_RATE), .freq(freq))
  baud_rate_generator_sva_i (
    .clk(clk),
    .rst_n(rst_n),
    .bps_start(bps_start),
    .clk_baud(clk_baud),
    .counter(counter),
    .toggle(toggle)
  );