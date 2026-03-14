module frequency_counter_sva (
  input logic clk,
  input logic sysclk,
  input logic read,
  input logic write,
  input logic pawr,
  input logic pard,
  input logic refresh,
  input logic cpuclk,
  input logic romsel,
  input logic cicclk,
  input logic [31:0] snes_sysclk_freq,
  input logic [31:0] snes_read_freq,
  input logic [31:0] snes_write_freq,
  input logic [31:0] snes_pawr_freq,
  input logic [31:0] snes_pard_freq,
  input logic [31:0] snes_refresh_freq,
  input logic [31:0] snes_cpuclk_freq,
  input logic [31:0] snes_romsel_freq,
  input logic [31:0] snes_cicclk_freq,

  // Internal state from RTL
  input logic [31:0] sysclk_counter,
  input logic [31:0] sysclk_value,
  input logic [31:0] read_value,
  input logic [31:0] write_value,
  input logic [31:0] pard_value,
  input logic [31:0] pawr_value,
  input logic [31:0] refresh_value,
  input logic [31:0] cpuclk_value,
  input logic [31:0] romsel_value,
  input logic [31:0] cicclk_value,

  input logic [1:0] sysclk_sreg,
  input logic [1:0] read_sreg,
  input logic [1:0] write_sreg,
  input logic [1:0] pard_sreg,
  input logic [1:0] pawr_sreg,
  input logic [1:0] refresh_sreg,
  input logic [1:0] cpuclk_sreg,
  input logic [1:0] romsel_sreg,
  input logic [1:0] cicclk_sreg,

  input logic sysclk_rising,
  input logic read_rising,
  input logic write_rising,
  input logic pard_rising,
  input logic pawr_rising,
  input logic refresh_rising,
  input logic cpuclk_rising,
  input logic romsel_rising,
  input logic cicclk_rising
);
  // Window and scale constants used in RTL
  localparam int unsigned WINDOW = 32'd96000000;
  localparam int unsigned SCALE  = 32'd1000000;

  ///// Sysclk counter behavior /////
  // sysclk_counter is never greater than WINDOW.
  check_counter_within_window: assert property (
    @(posedge clk) (sysclk_counter <= WINDOW)
  );

  // While counting (sysclk_counter < WINDOW), sysclk_counter increments by 1 each cycle.
  check_counter_increment_when_counting: assert property (
    @(posedge clk) (sysclk_counter < WINDOW) |=> (sysclk_counter == $past(sysclk_counter) + 32'd1)
  );

  // On rollover cycle (sysclk_counter >= WINDOW), next cycle resets all event counters and sysclk_counter to 0.
  check_rollover_resets_all_counters: assert property (
    @(posedge clk) (sysclk_counter >= WINDOW) |=> (
      (sysclk_counter == 32'd0) &&
      (sysclk_value == 32'd0) && (read_value == 32'd0) && (write_value == 32'd0) &&
      (pard_value == 32'd0) && (pawr_value == 32'd0) && (refresh_value == 32'd0) &&
      (cpuclk_value == 32'd0) && (romsel_value == 32'd0) && (cicclk_value == 32'd0)
    )
  );

  ///// Output behavior /////
  // During counting phase, the frequency outputs hold their previous values.
  check_outputs_stable_while_counting: assert property (
    @(posedge clk) (sysclk_counter < WINDOW) |=> (
      (snes_sysclk_freq  == $past(snes_sysclk_freq))  &&
      (snes_read_freq    == $past(snes_read_freq))    &&
      (snes_write_freq   == $past(snes_write_freq))   &&
      (snes_pard_freq    == $past(snes_pard_freq))    &&
      (snes_pawr_freq    == $past(snes_pawr_freq))    &&
      (snes_refresh_freq == $past(snes_refresh_freq)) &&
      (snes_cpuclk_freq  == $past(snes_cpuclk_freq))  &&
      (snes_romsel_freq  == $past(snes_romsel_freq))  &&
      (snes_cicclk_freq  == $past(snes_cicclk_freq))
    )
  );

  // On rollover, snes_sysclk_freq updates to (prev sysclk_value * SCALE) / WINDOW.
  check_snes_sysclk_freq_update_on_rollover: assert property (
    @(posedge clk) (sysclk_counter >= WINDOW) |=> (
      snes_sysclk_freq == ($past(sysclk_value) * SCALE) / WINDOW
    )
  );
  // On rollover, snes_read_freq updates to (prev read_value * SCALE) / WINDOW.
  check_snes_read_freq_update_on_rollover: assert property (
    @(posedge clk) (sysclk_counter >= WINDOW) |=> (
      snes_read_freq == ($past(read_value) * SCALE) / WINDOW
    )
  );
  // On rollover, snes_write_freq updates to (prev write_value * SCALE) / WINDOW.
  check_snes_write_freq_update_on_rollover: assert property (
    @(posedge clk) (sysclk_counter >= WINDOW) |=> (
      snes_write_freq == ($past(write_value) * SCALE) / WINDOW
    )
  );
  // On rollover, snes_pard_freq updates to (prev pard_value * SCALE) / WINDOW.
  check_snes_pard_freq_update_on_rollover: assert property (
    @(posedge clk) (sysclk_counter >= WINDOW) |=> (
      snes_pard_freq == ($past(pard_value) * SCALE) / WINDOW
    )
  );
  // On rollover, snes_pawr_freq updates to (prev pawr_value * SCALE) / WINDOW.
  check_snes_pawr_freq_update_on_rollover: assert property (
    @(posedge clk) (sysclk_counter >= WINDOW) |=> (
      snes_pawr_freq == ($past(pawr_value) * SCALE) / WINDOW
    )
  );
  // On rollover, snes_refresh_freq updates to (prev refresh_value * SCALE) / WINDOW.
  check_snes_refresh_freq_update_on_rollover: assert property (
    @(posedge clk) (sysclk_counter >= WINDOW) |=> (
      snes_refresh_freq == ($past(refresh_value) * SCALE) / WINDOW
    )
  );
  // On rollover, snes_cpuclk_freq updates to (prev cpuclk_value * SCALE) / WINDOW.
  check_snes_cpuclk_freq_update_on_rollover: assert property (
    @(posedge clk) (sysclk_counter >= WINDOW) |=> (
      snes_cpuclk_freq == ($past(cpuclk_value) * SCALE) / WINDOW
    )
  );
  // On rollover, snes_romsel_freq updates to (prev romsel_value * SCALE) / WINDOW.
  check_snes_romsel_freq_update_on_rollover: assert property (
    @(posedge clk) (sysclk_counter >= WINDOW) |=> (
      snes_romsel_freq == ($past(romsel_value) * SCALE) / WINDOW
    )
  );
  // On rollover, snes_cicclk_freq updates to (prev cicclk_value * SCALE) / WINDOW.
  check_snes_cicclk_freq_update_on_rollover: assert property (
    @(posedge clk) (sysclk_counter >= WINDOW) |=> (
      snes_cicclk_freq == ($past(cicclk_value) * SCALE) / WINDOW
    )
  );

  ///// Event counters (examples) /////
  // sysclk_value increments by 1 on sysclk_rising during counting.
  check_sysclk_value_inc_on_rise: assert property (
    @(posedge clk) ((sysclk_counter < WINDOW) && sysclk_rising) |=> (sysclk_value == $past(sysclk_value) + 32'd1)
  );
  // sysclk_value holds when no sysclk_rising during counting.
  check_sysclk_value_hold_without_rise: assert property (
    @(posedge clk) ((sysclk_counter < WINDOW) && !sysclk_rising) |=> (sysclk_value == $past(sysclk_value))
  );

  // read_value increments by 1 on read_rising during counting.
  check_read_value_inc_on_rise: assert property (
    @(posedge clk) ((sysclk_counter < WINDOW) && read_rising) |=> (read_value == $past(read_value) + 32'd1)
  );
  // read_value holds when no read_rising during counting.
  check_read_value_hold_without_rise: assert property (
    @(posedge clk) ((sysclk_counter < WINDOW) && !read_rising) |=> (read_value == $past(read_value))
  );

  // write_value increments by 1 on write_rising during counting.
  check_write_value_inc_on_rise: assert property (
    @(posedge clk) ((sysclk_counter < WINDOW) && write_rising) |=> (write_value == $past(write_value) + 32'd1)
  );
  // write_value holds when no write_rising during counting.
  check_write_value_hold_without_rise: assert property (
    @(posedge clk) ((sysclk_counter < WINDOW) && !write_rising) |=> (write_value == $past(write_value))
  );

endmodule