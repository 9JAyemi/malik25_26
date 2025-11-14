// SVA for FFType_546
module FFType_546_sva (
  input logic        clock,
  input logic        reset,        // synchronous, active-high
  input logic [39:0] io_in,
  input logic [39:0] io_out,
  input logic        io_enable,
  input logic [39:0] ff_reg        // internal reg, connect via bind
);

  // Output must always reflect combinational mux
  assert property (@(posedge clock)
    io_out == (io_enable ? ff_reg : io_in))
  else $error("io_out mux mismatch");

  // Synchronous reset must clear ff_reg on the following cycle
  assert property (@(posedge clock)
    reset |=> (ff_reg == '0))
  else $error("ff_reg not cleared after reset");

  // When enabled, ff_reg captures io_in on next cycle
  assert property (@(posedge clock)
    disable iff (reset)
    io_enable |=> (ff_reg == $past(io_in)))
  else $error("ff_reg did not capture io_in when enabled");

  // When disabled, ff_reg holds its value
  assert property (@(posedge clock)
    disable iff (reset)
    !io_enable |=> (ff_reg == $past(ff_reg)))
  else $error("ff_reg changed while disabled");

  // Basic X checks on critical control/output
  assert property (@(posedge clock)
    disable iff (reset)
    !$isunknown(io_enable))
  else $error("io_enable is X/Z");

  assert property (@(posedge clock)
    disable iff (reset)
    !$isunknown(io_out))
  else $error("io_out is X/Z");

  // Coverage
  cover property (@(posedge clock) reset ##1 !reset);                         // exit reset
  cover property (@(posedge clock) disable iff (reset) !io_enable && (io_out == io_in)); // passthrough
  cover property (@(posedge clock) disable iff (reset) io_enable && (io_out == ff_reg)); // reg path
  cover property (@(posedge clock) disable iff (reset) io_enable ##1 (ff_reg == $past(io_in))); // capture
  cover property (@(posedge clock) disable iff (reset) !io_enable ##1 (ff_reg == $past(ff_reg))); // hold

endmodule

// Bind example (place in a separate file or a testbench)
// bind FFType_546 FFType_546_sva sva (
//   .clock(clock),
//   .reset(reset),
//   .io_in(io_in),
//   .io_out(io_out),
//   .io_enable(io_enable),
//   .ff_reg(ff_reg)
// );