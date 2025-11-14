// SVA for register modules (active-low synchronous reset, active-low write-enable)
// Concise, high-quality checks + basic coverage

module reg_assert #(parameter int W=1)
(
  input logic                clk,
  input logic                reset,   // active-low
  input logic                write,   // active-low WE (0=load, 1=hold)
  input logic [W-1:0]        in,
  input logic [W-1:0]        out
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity on controls and load data
  a_ctrl_known: assert property (disable iff ($initstate) !$isunknown({reset,write}));
  a_in_known_on_load: assert property (disable iff ($initstate) (reset && !write) |-> !$isunknown(in));

  // Functional semantics
  // Reset dominates and clears to zero on the next cycle
  a_reset_clear: assert property (disable iff ($initstate) (!reset) |=> (out == '0));
  // Explicit precedence when both reset=0 and write=0
  a_reset_over_write: assert property (disable iff ($initstate) (!reset && !write) |=> (out == '0));

  // Load on write=0 (when not in reset)
  a_load_on_we0: assert property (disable iff ($initstate) (reset && !write) |=> (out == $past(in)));

  // Hold when write=1 (when not in reset)
  a_hold_on_we1: assert property (disable iff ($initstate) (reset && write) |=> (out == $past(out)));

  // Any change must be caused by reset low or a load
  a_change_has_cause: assert property (disable iff ($initstate)
    (out != $past(out)) |-> ( !$past(reset) || ($past(reset) && !$past(write)) )
  );

  // Coverage: see reset, load, and hold behaviors
  c_reset: cover property (disable iff ($initstate) !reset);
  c_load:  cover property (disable iff ($initstate) (reset && !write) ##1 (out == $past(in)));
  c_hold:  cover property (disable iff ($initstate) (reset && write)  ##1 (out == $past(out)));
endmodule

// Bind to each DUT
bind register16 reg_assert #(.W(16)) reg16_chk (.clk(clk), .reset(reset), .write(write), .in(in), .out(out));
bind register4  reg_assert #(.W(4 )) reg4_chk  (.clk(clk), .reset(reset), .write(write), .in(in), .out(out));
bind register3  reg_assert #(.W(3 )) reg3_chk  (.clk(clk), .reset(reset), .write(write), .in(in), .out(out));
bind register2  reg_assert #(.W(2 )) reg2_chk  (.clk(clk), .reset(reset), .write(write), .in(in), .out(out));
bind register1  reg_assert #(.W(1 )) reg1_chk  (.clk(clk), .reset(reset), .write(write), .in(in), .out(out));